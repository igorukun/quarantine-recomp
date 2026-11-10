// System layer: DOS (int 21h), DPMI (int 31h), BIOS, selectors, PIC/PIT, keyboard, VGA (Mode X),
// and the SDL3 host frontend.
#include "compat.h"
#include "rt.h"
#include "sys.h"
#include "disc.h"
#include "../gen/image_info.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>
#include <ctype.h>
#ifdef USE_SDL
#include <SDL3/SDL.h>
#endif

static int verbose;
#define LOG(...) do { if (verbose) fprintf(stderr, __VA_ARGS__); } while (0)

static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

// ================================================================ low memory layout
#define PSP_SEG   0x0100
#define PSP_LIN   (PSP_SEG << 4)
#define ENV_LIN   0x1200
#define DOSMEM_LO 0x2000
#define DOSMEM_HI 0x9F000
#define HEAP_LO   0x00400000u
static uint32_t dos_brk = DOSMEM_LO;
static uint32_t heap_brk = HEAP_LO;

// ================================================================ selectors (LDT)
#define NSEL 512
struct desc { uint32_t base, limit; uint16_t access; uint8_t used; };
static struct desc ldt[NSEL];
static inline int sel_idx(uint16_t sel) { return sel >> 3; }
uint32_t sel_base(uint16_t sel) {
    int i = sel_idx(sel);
    if (sel <= 3) return 0;   // selectors 1..3 = LE object numbers from 16:32 fixups (flat)
    if (i < NSEL && ldt[i].used) return ldt[i].base;
    return 0;
}
void set_sreg(int s, uint16_t sel) { S[s] = sel; SB[s] = sel_base(sel); }
static void refresh_sregs(void) { for (int s = 0; s < 6; s++) SB[s] = sel_base(S[s]); }
static void def_sel(uint16_t sel, uint32_t base, uint32_t limit, uint16_t acc) {
    struct desc *d = &ldt[sel_idx(sel)]; d->base = base; d->limit = limit; d->access = acc; d->used = 1;
}
static int alloc_sels(int n) {
    for (int i = 0x40; i + n <= NSEL; i++) {
        int ok = 1;
        for (int k = 0; k < n; k++) if (ldt[i + k].used) { ok = 0; break; }
        if (!ok) continue;
        for (int k = 0; k < n; k++) { ldt[i + k].used = 1; ldt[i + k].base = 0; ldt[i + k].limit = 0; ldt[i + k].access = 0x92; }
        return (i << 3) | 7;
    }
    return -1;
}
int rt_lsl(uint32_t sel, uint32_t *out) {
    int i = sel_idx(sel);
    if (i >= NSEL || !ldt[i].used) return 0;
    if (out) *out = ldt[i].limit;
    return 1;
}
int rt_lar(uint32_t sel, uint32_t *out) {
    int i = sel_idx(sel);
    if (i >= NSEL || !ldt[i].used) return 0;
    if (out) *out = (uint32_t)ldt[i].access << 8 | 0x00c00000u;
    return 1;
}

// ================================================================ interrupt vectors
static uint32_t pm_vec[256];
static uint32_t rm_vec[256];
uint32_t sys_pm_vector(int vec) { return pm_vec[vec]; }

// ================================================================ PIC / PIT / IRQ queue
static atomic_int irq_req;             // bit0 timer, bit1 keyboard
static uint8_t pic_mask = 0;
static uint32_t pit_divisor = 65536;
static int pit_latch_lo = 1;
static uint16_t pit_reload_tmp;
static double pit_rate(void) { return 1193182.0 / (pit_divisor ? pit_divisor : 65536); }

#define KBQ 64
static uint8_t kbq[KBQ]; static int kbq_r, kbq_w; static uint8_t kb_last;
static void kb_push(uint8_t sc) { if (((kbq_w + 1) & (KBQ - 1)) != kbq_r) { kbq[kbq_w] = sc; kbq_w = (kbq_w + 1) & (KBQ - 1); } }
void sys_key(uint8_t sc, int down) { kb_push(down ? sc : sc | 0x80); }   // used by rt_pad.c

static uint32_t timer_ticks_owed;   // guest timer interrupts not yet delivered
static double bios_tick_acc;

int sys_irq_waiting(void) { return timer_ticks_owed || kbq_r != kbq_w; }
static int kb_hold(void);
int sys_next_irq(void) {
    if (timer_ticks_owed && !(pic_mask & 1)) {
        timer_ticks_owed--;
        return 8;
    }
    if (kbq_r != kbq_w && !(pic_mask & 2)) {
        uint8_t next_sc = kbq[kbq_r];

        // 0xE0 (префикс расширенных клавиш) и отпускания — сразу
        // Нажатия — через kb_hold
        if (next_sc == 0xe0 || (next_sc & 0x80) || !kb_hold()) {
            kb_last = next_sc;
            kbq_r = (kbq_r + 1) & (KBQ - 1);
            return 9;
        }
    }
    return -1;
}

// ================================================================ VGA
static uint8_t planes[4][65536];
static uint8_t latch[4];
static uint8_t seq_idx, seq[8] = {0, 0, 0x0f, 0, 0x0e};
static uint8_t gc_idx, gc[16] = {[8] = 0xff};
static uint8_t crtc_idx, crtc[32] = {[0x13] = 40, [0x09] = 0x41, [0x12] = 0x8f};
static uint8_t att_idx, att[32], att_flip;
static uint8_t dac[256][3], dac_widx, dac_ridx, dac_comp, dac_rcomp;
static int vga_mode = 3;
static double retrace_t0;
static uint64_t flip_count;
static int no_vsync;
static int pad_on;
static uint32_t watch_addr;
// The game never waits for retrace: it flips pages as fast as it can draw (thousands per second on a
// modern CPU). A real VGA shows at most one new page per 70 Hz refresh, so pace page flips (writes of
// the CRTC start-address high byte) to 70 per second. QUAR_NOVSYNC=1 turns this off.
//
// Sleeping here moves all of a frame's idle time to one point, where no interrupts are delivered, so a
// key pressed during the sleep would always reach the game right after the flip. The menus call kbhit()
// at the top of their loop, which swallows the key before the menu's own check later in the frame. On
// real hardware a key arrives at a random point of the frame (mostly during the long screen copy), so
// hold keyboard interrupts until the game is halfway through the next frame's work (kb_hold).
static double flip_end_t, frame_work;
static void vga_flip(void) {
    static double next;
    flip_count++;
    if (no_vsync) return;
    double t = now_s();
    frame_work = t - flip_end_t;
    if (t < next) {
        host_sleep_ns((uint64_t)((next - t) * 1e9));
        next += 1.0 / 70;
    } else next = (t - next > 1.0 / 70 ? t : next) + 1.0 / 70;
    flip_end_t = now_s();
}
static int kb_hold(void) {
    if (no_vsync) return 0;
    double since = now_s() - flip_end_t;
    return since < 0.001;
}

static inline int chain4(void) { return (seq[4] & 0x08) != 0; }
uint8_t vga_read(uint32_t a) {
    uint32_t off = a - 0xA0000;
    if (chain4()) return planes[off & 3][off >> 2];
    for (int p = 0; p < 4; p++) latch[p] = planes[p][off];
    return planes[gc[4] & 3][off];
}
static uint64_t vga_wcount;
void vga_write(uint32_t a, uint8_t v) {
    uint32_t off = a - 0xA0000; vga_wcount++;
    if (chain4()) { planes[off & 3][off >> 2] = v; return; }
    uint8_t mask = seq[2] & 0x0f;
    int mode = gc[5] & 3;
    for (int p = 0; p < 4; p++) {
        if (!(mask & (1 << p))) continue;
        if (mode == 1) planes[p][off] = latch[p];
        else {
            uint8_t bm = gc[8];
            planes[p][off] = (v & bm) | (latch[p] & ~bm);
        }
    }
}
static uint8_t vga_in(uint32_t port) {
    switch (port) {
    case 0x3c4: return seq_idx;
    case 0x3c5: return seq[seq_idx & 7];
    case 0x3ce: return gc_idx;
    case 0x3cf: return gc[gc_idx & 15];
    case 0x3d4: return crtc_idx;
    case 0x3d5: return crtc[crtc_idx & 31];
    case 0x3c9: { uint8_t v = dac[dac_ridx][dac_rcomp]; if (++dac_rcomp == 3) { dac_rcomp = 0; dac_ridx++; } return v; }
    case 0x3da: {
        att_flip = 0;
        double ph = fmod((now_s() - retrace_t0) * 70.0, 1.0);
        return ph > 0.9 ? 0x09 : (ph > 0.75 ? 0x01 : 0x00);
    }
    case 0x3cc: return 0x63;
    }
    return 0xff;
}
static void vga_out(uint32_t port, uint8_t v) {
    switch (port) {
    case 0x3c4: seq_idx = v; break;
    case 0x3c5: seq[seq_idx & 7] = v; break;
    case 0x3ce: gc_idx = v; break;
    case 0x3cf: gc[gc_idx & 15] = v; break;
    case 0x3d4: crtc_idx = v; break;
    case 0x3d5: crtc[crtc_idx & 31] = v; if ((crtc_idx & 31) == 0x0c) vga_flip(); break;
    case 0x3c0: if (!att_flip) att_idx = v; else att[att_idx & 31] = v; att_flip ^= 1; break;
    case 0x3c7: dac_ridx = v; dac_rcomp = 0; break;
    case 0x3c8: dac_widx = v; dac_comp = 0; if (verbose) { static int n; if (n++ < 30) fprintf(stderr, "DAC write index %d\n", v); if (n == 5) rt_trace_dump(stderr); } break;
    case 0x3c9: dac[dac_widx][dac_comp] = v & 63; if (++dac_comp == 3) { dac_comp = 0; dac_widx++; } break;
    }
}
static void vga_set_mode(int mode) {
    vga_mode = mode;
    memset(planes, 0, sizeof planes);
    if (mode == 0x13) {
        seq[2] = 0x0f; seq[4] = 0x0e; gc[5] = 0x40; gc[8] = 0xff; crtc[0x13] = 40; crtc[0x14] = 0x40; crtc[0x17] = 0xa3;
        crtc[0x0c] = crtc[0x0d] = 0; crtc[0x09] = 0x41; crtc[0x12] = 0x8f; crtc[0x06] = 0xbf; crtc[0x07] = 0x1f;
        for (int i = 0; i < 256; i++) { dac[i][0] = dac[i][1] = dac[i][2] = (uint8_t)((i & 63)); }
    }
}
#define SCR_W 320
static int scr_h = 200;
static uint32_t framebuf[320 * 240];
static void vga_render(void) {
    int h = 200;
    // vertical display end (8 bits + overflow bits 1/6) / (scanline doubling)
    int vde = crtc[0x12] | ((crtc[0x07] & 0x02) << 7) | ((crtc[0x07] & 0x40) << 3);
    int maxscan = (crtc[0x09] & 0x1f) + 1;
    if (crtc[0x09] & 0x80) maxscan *= 2;
    if (vga_mode == 0x13 && maxscan) h = (vde + 1) / maxscan;
    if (h > 240) h = 240;
    if (h < 100) h = 200;
    scr_h = h;
    uint32_t pal[256];
    for (int i = 0; i < 256; i++) {
        uint32_t r = dac[i][0], g = dac[i][1], b = dac[i][2];
        pal[i] = 0xff000000u | ((r << 2 | r >> 4) << 16) | ((g << 2 | g >> 4) << 8) | (b << 2 | b >> 4);
    }
    uint32_t start = (crtc[0x0c] << 8) | crtc[0x0d];
    uint32_t pitch = crtc[0x13] * 2;
    for (int y = 0; y < h; y++)
        for (int x = 0; x < SCR_W; x++) {
            uint8_t c;
            if (chain4()) { uint32_t o = y * 320 + x; c = planes[o & 3][(o >> 2) & 0xffff]; }
            else c = planes[x & 3][(start + y * pitch + (x >> 2)) & 0xffff];
            framebuf[y * SCR_W + x] = pal[c];
        }
}

// ================================================================ ports
uint32_t rt_in8(uint32_t port) {
    port &= 0xffff;
    if (port >= 0x3c0 && port <= 0x3df) return vga_in(port);
    switch (port) {
    case 0x60: return kb_last;
    case 0x61: return 0;
    case 0x64: return 0x14;
    case 0x21: return pic_mask;
    case 0x20: return 0;
    case 0x40: return 0;
    case 0x201: return 0xf0;  // no joystick: axis bits never go high
    }
    LOG("in8 %x\n", port);
    return 0xff;
}
uint32_t rt_in16(uint32_t port) { return rt_in8(port) | (rt_in8(port + 1) << 8); }
uint32_t rt_in32(uint32_t port) { return rt_in16(port) | (rt_in16(port + 2) << 16); }
void rt_out8(uint32_t port, uint32_t v) {
    port &= 0xffff; v &= 0xff;
    if (port >= 0x3c0 && port <= 0x3df) { vga_out(port, v); return; }
    switch (port) {
    case 0x20: case 0xa0: return;              // EOI
    case 0x21: pic_mask = v; return;
    case 0x43: pit_latch_lo = 1; return;
    case 0x40:
        if (pit_latch_lo) { pit_reload_tmp = v; pit_latch_lo = 0; }
        else { pit_reload_tmp |= v << 8; pit_divisor = pit_reload_tmp ? pit_reload_tmp : 65536; pit_latch_lo = 1;
               LOG("PIT rate %.1f Hz\n", pit_rate()); }
        return;
    case 0x61: case 0x201: return;
    }
    LOG("out8 %x,%x\n", port, v);
}
void rt_out16(uint32_t port, uint32_t v) { rt_out8(port, v & 0xff); rt_out8(port + 1, (v >> 8) & 0xff); }
void rt_out32(uint32_t port, uint32_t v) { rt_out16(port, v & 0xffff); rt_out16(port + 2, v >> 16); }

// ================================================================ files
static char data_dir[1024] = "extracted/cd", save_dir[1024] = "save";
static int dos_fd[64];
static int find_ci(const char *dir, const char *name, char *out, size_t n) {
    DIR *d = opendir(dir); if (!d) return 0;
    struct dirent *e; int ok = 0;
    while ((e = readdir(d))) if (!strcasecmp(e->d_name, name)) { snprintf(out, n, "%s/%s", dir, e->d_name); ok = 1; break; }
    closedir(d); return ok;
}
// DOS path -> host path. Only the last component matters for this game (flat directory).
static const char *base_of(const char *p) {
    const char *b = p;
    for (const char *q = p; *q; q++) if (*q == '\\' || *q == '/' || *q == ':') b = q + 1;
    return b;
}
static int host_path(const char *dos, char *out, size_t n, int for_write) {
    const char *b = base_of(dos);
    if (find_ci(save_dir, b, out, n)) return 1;
    if (!for_write && find_ci(data_dir, b, out, n)) return 1;
    char low[256]; size_t k = 0; for (; b[k] && k < 255; k++) low[k] = toupper((unsigned char)b[k]); low[k] = 0;
    snprintf(out, n, "%s/%s", save_dir, low);
    return 0;
}
static int copy_file(const char *src, const char *dst) {
    int in = open(src, O_RDONLY | O_BINARY); if (in < 0) return -1;
    int out = open(dst, O_WRONLY | O_BINARY | O_CREAT | O_TRUNC, 0644); if (out < 0) { close(in); return -1; }
    char buf[65536]; ssize_t r; int rc = 0;
    while ((r = read(in, buf, sizeof buf)) > 0) if (write(out, buf, r) != r) { rc = -1; break; }
    close(in); close(out); return rc;
}
static void read_cstr(uint32_t a, char *out, int n) { int k = 0; for (; k < n - 1; k++) { out[k] = RD8(a + k); if (!out[k]) break; } out[k] = 0; }
static int new_handle(int fd) { for (int h = 5; h < 64; h++) if (dos_fd[h] < 0) { dos_fd[h] = fd; return h; } return -1; }

struct findst { uint32_t dta; char pat[64]; DIR *d; int stage; uint8_t attr; };
static struct findst fst;
static uint32_t dta_addr = PSP_LIN + 0x80;
static int find_next_entry(void) {
    for (;;) {
        if (!fst.d) {
            if (fst.stage == 0) fst.d = opendir(save_dir);
            else if (fst.stage == 1) fst.d = opendir(data_dir);
            else return 0;
            fst.stage++;
            if (!fst.d) continue;
        }
        struct dirent *e = readdir(fst.d);
        if (!e) { closedir(fst.d); fst.d = 0; continue; }
        if (e->d_name[0] == '.') continue;
        if (fnmatch(fst.pat, e->d_name, FNM_CASEFOLD)) continue;
        char hp[2048]; struct stat st;
        snprintf(hp, sizeof hp, "%s/%s", fst.stage == 1 ? save_dir : data_dir, e->d_name);
        if (stat(hp, &st) || !S_ISREG(st.st_mode)) continue;
        uint32_t d = fst.dta;
        WR8(d + 0x15, 0x20); WR16(d + 0x16, 0); WR16(d + 0x18, (14 << 9) | (1 << 5) | 1);
        WR32(d + 0x1a, (uint32_t)st.st_size);
        for (int k = 0; k < 13; k++) WR8(d + 0x1e + k, 0);
        for (int k = 0; e->d_name[k] && k < 12; k++) WR8(d + 0x1e + k, toupper((unsigned char)e->d_name[k]));
        return 1;
    }
}

// ================================================================ DOS int 21h
#define AL ((uint8_t)EAX)
#define AH ((uint8_t)(EAX >> 8))
#define SETAX(v) (EAX = (EAX & 0xffff0000u) | ((v) & 0xffff))
#define SETAL(v) (EAX = (EAX & 0xffffff00u) | ((v) & 0xff))
static void ok(void) { set_cf(0); }
static void err(int code) { SETAX(code); set_cf(1); }
static int exit_requested = 0;

static void dos_int21(void) {
    char name[256], hp[2048];
    switch (AH) {
    case 0x02: putchar(EDX & 0xff); fflush(stdout); return;
    case 0x06: if ((EDX & 0xff) == 0xff) { SETAL(0); set_zf(1); } else putchar(EDX & 0xff); return;
    case 0x07: case 0x08: SETAL(0x0d); return;
    case 0x09: { uint32_t a = SB[3] + EDX; char c; while ((c = RD8(a++)) != '$') putchar(c); fflush(stdout); return; }
    case 0x0b: SETAL(0); return;
    case 0x0e: SETAL(26); return;
    case 0x19: SETAL(2); return;                       // C:
    case 0x1a: dta_addr = SB[3] + EDX; return;
    case 0x2f: set_sreg(0, SEL_DATA); EBX = dta_addr; return;
    case 0x25: pm_vec[AL] = EDX; LOG("set vector %02x -> %08x\n", AL, EDX); return;
    case 0x35: set_sreg(0, SEL_CODE); EBX = pm_vec[AL]; return;
    case 0x2a: { time_t t = time(0); struct tm *tm = localtime(&t); ECX = (ECX & 0xffff0000u) | (tm->tm_year + 1900);
                 EDX = (EDX & 0xffff0000u) | ((tm->tm_mon + 1) << 8) | tm->tm_mday; SETAL(tm->tm_wday); return; }
    case 0x2c: { struct timespec ts; clock_gettime(CLOCK_REALTIME, &ts); struct tm *tm = localtime(&ts.tv_sec);
                 ECX = (ECX & 0xffff0000u) | (tm->tm_hour << 8) | tm->tm_min;
                 EDX = (EDX & 0xffff0000u) | (tm->tm_sec << 8) | (uint8_t)(ts.tv_nsec / 10000000); return; }
    case 0x30: EAX = 0x44580005; return;              // DOS 5.0 + "DX" = DOS/4G
    case 0x33: EDX &= ~0xffu; return;
    case 0x36: SETAX(64); EBX = (EBX & 0xffff0000u) | 0x7fff; ECX = (ECX & 0xffff0000u) | 512; EDX = (EDX & 0xffff0000u) | 0xffff; return;
    case 0x37: if (AL == 0) { EDX = (EDX & ~0xffu) | '/'; SETAL(0); } else SETAL(0); return;
    case 0x3b: ok(); return;
    case 0x47: WR8(SB[3] + ESI, 0); ok(); return;
    case 0x3c: case 0x5b: {
        read_cstr(SB[3] + EDX, name, sizeof name); host_path(name, hp, sizeof hp, 1);
        int fd = open(hp, O_RDWR | O_BINARY | O_CREAT | O_TRUNC, 0644);
        LOG("create %s -> %s fd %d\n", name, hp, fd);
        if (fd < 0) { err(3); return; }
        SETAX(new_handle(fd)); ok(); return;
    }
    case 0x3d: {
        read_cstr(SB[3] + EDX, name, sizeof name);
        int found = host_path(name, hp, sizeof hp, 0);
        int mode = AL & 3;
        int fd = -1;
        if (found && mode && strncmp(hp, save_dir, strlen(save_dir)) != 0) {
            // Opened for writing but it only exists in the game-data directory: copy it to the save
            // directory first so the game's files are never modified (copy-on-write).
            char dst[2048]; host_path(name, dst, sizeof dst, 1);
            if (copy_file(hp, dst) == 0) { LOG("copy-on-write %s -> %s\n", hp, dst); snprintf(hp, sizeof hp, "%s", dst); }
        }
        if (found) {
            fd = open(hp, mode == 0 ? O_RDONLY | O_BINARY : O_RDWR | O_BINARY);
            if (fd < 0 && mode) fd = open(hp, O_RDONLY | O_BINARY);
        }
        LOG("open %s (mode %d) -> %s fd %d\n", name, mode, found ? hp : "(not found)", fd);
        if (fd < 0) { err(2); return; }
        SETAX(new_handle(fd)); ok(); return;
    }
    case 0x3e: { int h = EBX & 0xffff; if (h >= 5 && h < 64 && dos_fd[h] >= 0) { close(dos_fd[h]); dos_fd[h] = -1; } ok(); return; }
    case 0x3f: {
        int h = EBX & 0xffff;
        if (h == 0) { EAX = 0; ok(); return; }
        if (h >= 64 || dos_fd[h] < 0) { err(6); return; }
        uint32_t a = SB[3] + EDX, n = ECX;
        ssize_t r;
        if (IS_VGA(a) || a + n > MEM_SIZE) { uint8_t *tmp = malloc(n); r = read(dos_fd[h], tmp, n); for (ssize_t k = 0; k < r; k++) WR8(a + k, tmp[k]); free(tmp); }
        else r = read(dos_fd[h], MEM + a, n);
        if (r < 0) { err(5); return; }
        EAX = (uint32_t)r; ok(); return;
    }
    case 0x40: {
        int h = EBX & 0xffff; uint32_t a = SB[3] + EDX, n = ECX;
        if (h == 1 || h == 2) { fwrite(MEM + a, 1, n, h == 1 ? stdout : stderr); EAX = n; ok(); return; }
        if (h >= 64 || dos_fd[h] < 0) { err(6); return; }
        ssize_t r = write(dos_fd[h], MEM + a, n);
        if (r < 0) { err(5); return; }
        EAX = (uint32_t)r; ok(); return;
    }
    case 0x41: read_cstr(SB[3] + EDX, name, sizeof name); if (host_path(name, hp, sizeof hp, 1)) unlink(hp); ok(); return;
    case 0x42: {
        int h = EBX & 0xffff; if (h >= 64 || dos_fd[h] < 0) { err(6); return; }
        off_t off = (off_t)(int32_t)(((ECX & 0xffff) << 16) | (EDX & 0xffff));
        off_t r = lseek(dos_fd[h], off, AL == 0 ? SEEK_SET : AL == 1 ? SEEK_CUR : SEEK_END);
        if (r < 0) { err(25); return; }
        SETAX((uint32_t)r); EDX = (EDX & 0xffff0000u) | (((uint32_t)r >> 16) & 0xffff); ok(); return;
    }
    case 0x43: read_cstr(SB[3] + EDX, name, sizeof name);
        if (!host_path(name, hp, sizeof hp, 0)) { err(2); return; }
        ECX = (ECX & 0xffff0000u) | 0x20; ok(); return;
    case 0x44:
        if (AL == 0) { int h = EBX & 0xffff; EDX = (EDX & 0xffff0000u) | (h < 5 ? 0x80d3 : 0x0002); ok(); return; }
        if (AL == 8) { SETAX(1); ok(); return; }
        err(1); return;
    case 0x45: { int h = EBX & 0xffff; if (h >= 64 || dos_fd[h] < 0) { err(6); return; } SETAX(new_handle(dup(dos_fd[h]))); ok(); return; }
    case 0x48: {   // DOS/4GW: allocate memory, BX paragraphs (rarely used by Watcom heap)
        uint32_t sz = (EBX & 0xffff) << 4; uint32_t lin = (heap_brk + 15) & ~15u; heap_brk = lin + sz;
        int s = alloc_sels(1); def_sel(s, lin, sz - 1, 0x92); SETAX(s); ok(); return;
    }
    case 0x49: ok(); return;
    case 0x4a: ok(); return;
    case 0x4b: {
        read_cstr(SB[3] + EDX, name, sizeof name);
        uint32_t pb = SB[0] + EBX; uint32_t tail = RD32(pb + 4) + sel_base(RD16(pb + 8));
        char t[130]; int n = RD8(tail); for (int k = 0; k < n && k < 127; k++) t[k] = RD8(tail + 1 + k); t[n < 127 ? n : 127] = 0;
        fprintf(stderr, "[EXEC %s args \"%s\" (al=%d) -> pretending success]\n", name, t, AL);
        SETAX(0); ok(); return;
    }
    case 0x4d: SETAX(0); ok(); return;
    case 0x4c: fprintf(stderr, "[guest exit %d]\n", AL); exit_requested = 1; sys_shutdown(); exit(AL);
    case 0x4e: {
        read_cstr(SB[3] + EDX, name, sizeof name);
        if (fst.d) closedir(fst.d);
        memset(&fst, 0, sizeof fst); fst.dta = dta_addr;
        snprintf(fst.pat, sizeof fst.pat, "%s", base_of(name));
        if (!strcmp(fst.pat, "*.*")) strcpy(fst.pat, "*");
        LOG("findfirst %s\n", name);
        if (find_next_entry()) ok(); else err(18);
        return;
    }
    case 0x4f: if (find_next_entry()) ok(); else err(18); return;
    case 0x56: {
        char n2[256], hp2[2048];
        read_cstr(SB[3] + EDX, name, sizeof name); read_cstr(SB[0] + EDI, n2, sizeof n2);
        host_path(name, hp, sizeof hp, 1); host_path(n2, hp2, sizeof hp2, 1);
        if (rename(hp, hp2)) err(5); else ok(); return;
    }
    case 0x57: if (AL == 0) { ECX &= 0xffff0000u; EDX = (EDX & 0xffff0000u) | ((14 << 9) | (1 << 5) | 1); } ok(); return;
    case 0x59: SETAX(0); return;
    case 0x62: EBX = (EBX & 0xffff0000u) | SEL_PSP; return;
    case 0x67: ok(); return;
    case 0xff: return;
    }
    rt_fatal("int 21h AH=%02x not implemented (eax=%08x)", AH, EAX);
}

// ================================================================ real-mode services (via DPMI 0300h)
struct rmregs { uint32_t edi, esi, ebp, res, ebx, edx, ecx, eax; uint16_t flags, es, ds, fs, gs, ip, cs, sp, ss; };
static void rm_load(uint32_t a, struct rmregs *r) {
    r->edi = RD32(a); r->esi = RD32(a + 4); r->ebp = RD32(a + 8); r->ebx = RD32(a + 16); r->edx = RD32(a + 20);
    r->ecx = RD32(a + 24); r->eax = RD32(a + 28); r->flags = RD16(a + 32); r->es = RD16(a + 34); r->ds = RD16(a + 36);
}
static void rm_store(uint32_t a, struct rmregs *r) {
    WR32(a, r->edi); WR32(a + 4, r->esi); WR32(a + 8, r->ebp); WR32(a + 16, r->ebx); WR32(a + 20, r->edx);
    WR32(a + 24, r->ecx); WR32(a + 28, r->eax); WR16(a + 32, r->flags); WR16(a + 34, r->es); WR16(a + 36, r->ds);
}
static int mouse_x = 160, mouse_y = 100, mouse_b;
static void int10(uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx) {
    uint8_t ah = (*eax >> 8) & 0xff, al = *eax & 0xff;
    switch (ah) {
    case 0x00: LOG("int10 set mode %02x\n", al); vga_set_mode(al & 0x7f); return;
    case 0x0f: *eax = (*eax & 0xffff0000u) | (40 << 8) | vga_mode; *ebx &= 0xffff00ffu; return;
    case 0x10:
        if (al == 0x10) { int i = *ebx & 0xff; dac[i][0] = (*edx >> 8) & 63; dac[i][1] = (*ecx >> 8) & 63; dac[i][2] = *ecx & 63; }
        return;
    case 0x11: case 0x12: case 0x01: case 0x02: case 0x03: case 0x05: case 0x06: case 0x09: case 0x0e: return;
    case 0x1a: *eax = (*eax & 0xffff0000u) | 0x1a; *ebx = (*ebx & 0xffff0000u) | 0x08; return;  // VGA present
    case 0x4f: *eax = (*eax & 0xffff0000u) | 0x0100; return;                                    // no VESA
    }
    LOG("int10 ah=%02x unhandled\n", ah);
}
static int int33(uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx) {
    switch (*eax & 0xffff) {
    case 0x00: *eax = (*eax & 0xffff0000u) | 0xffff; *ebx = (*ebx & 0xffff0000u) | 2; return 1;
    case 0x03: *ebx = (*ebx & 0xffff0000u) | mouse_b; *ecx = (*ecx & 0xffff0000u) | (mouse_x * 2); *edx = (*edx & 0xffff0000u) | mouse_y; return 1;
    case 0x0b: *ecx &= 0xffff0000u; *edx &= 0xffff0000u; return 1;
    default: return 1;
    }
}
static void rm_int(int n, uint32_t a) {
    struct rmregs r; rm_load(a, &r);
    if (n != 0x2f) LOG("RM int %02x ax=%04x bx=%04x cx=%04x dx=%04x es=%04x\n", n, r.eax & 0xffff, r.ebx & 0xffff, r.ecx & 0xffff, r.edx & 0xffff, r.es);
    r.flags &= ~1;
    switch (n) {
    case 0x10: int10(&r.eax, &r.ebx, &r.ecx, &r.edx); break;
    case 0x33: int33(&r.eax, &r.ebx, &r.ecx, &r.edx); break;
    case 0x2f:
        if (!cd_int2f(&r.eax, &r.ebx, &r.ecx, &r.edx, r.es)) LOG("RM int2f %04x\n", r.eax & 0xffff);
        break;
    case 0x21: LOG("RM int21 ah=%02x ignored\n", (r.eax >> 8) & 0xff); r.flags |= 1; break;
    default: LOG("RM int %02x ignored\n", n); break;
    }
    rm_store(a, &r);
}

// ================================================================ DPMI int 31h
static void dpmi(void) {
    uint16_t ax = EAX & 0xffff;
    int bx = EBX & 0xffff;
    switch (ax) {
    case 0x0000: { int s = alloc_sels(ECX & 0xffff); if (s < 0) { err(0x8011); return; } SETAX(s); LOG("alloc %d sel -> %x\n", ECX & 0xffff, s); ok(); return; }
    case 0x0001: if (sel_idx(bx) < NSEL) ldt[sel_idx(bx)].used = 0; ok(); return;
    case 0x0002: { int s = alloc_sels(1); def_sel(s, bx << 4, 0xffff, 0x92); SETAX(s); ok(); return; }
    case 0x0003: SETAX(8); ok(); return;
    case 0x0006: { uint32_t b = sel_base(bx); ECX = (ECX & 0xffff0000u) | (b >> 16); EDX = (EDX & 0xffff0000u) | (b & 0xffff); ok(); return; }
    case 0x0007: ldt[sel_idx(bx)].base = ((ECX & 0xffff) << 16) | (EDX & 0xffff); refresh_sregs();
                 LOG("set base %x = %x\n", bx, ldt[sel_idx(bx)].base); ok(); return;
    case 0x0008: ldt[sel_idx(bx)].limit = ((ECX & 0xffff) << 16) | (EDX & 0xffff); ok(); return;
    case 0x0009: ldt[sel_idx(bx)].access = ECX & 0xffff; ok(); return;
    case 0x000a: { int s = alloc_sels(1); ldt[sel_idx(s)] = ldt[sel_idx(bx)]; SETAX(s); ok(); return; }
    case 0x000b: { struct desc *d = &ldt[sel_idx(bx)]; uint32_t a = SB[0] + EDI;
                   WR16(a, d->limit & 0xffff); WR16(a + 2, d->base & 0xffff); WR8(a + 4, (d->base >> 16) & 0xff);
                   WR8(a + 5, d->access & 0xff); WR8(a + 6, ((d->limit >> 16) & 0x0f) | 0x40); WR8(a + 7, d->base >> 24); ok(); return; }
    case 0x000c: { struct desc *d = &ldt[sel_idx(bx)]; uint32_t a = SB[0] + EDI;
                   d->limit = RD16(a) | ((RD8(a + 6) & 0x0f) << 16); d->base = RD16(a + 2) | (RD8(a + 4) << 16) | (RD8(a + 7) << 24);
                   d->access = RD8(a + 5); d->used = 1; refresh_sregs(); ok(); return; }
    case 0x0100: {
        uint32_t sz = bx << 4; uint32_t lin = (dos_brk + 15) & ~15u;
        if (lin + sz > DOSMEM_HI) { EBX = (EBX & 0xffff0000u) | ((DOSMEM_HI - lin) >> 4); err(8); return; }
        dos_brk = lin + sz; int s = alloc_sels(1); def_sel(s, lin, sz - 1, 0x92);
        SETAX(lin >> 4); EDX = (EDX & 0xffff0000u) | s; LOG("DOS alloc %x bytes at %x sel %x\n", sz, lin, s); ok(); return;
    }
    case 0x0101: ok(); return;
    case 0x0102: ok(); return;
    case 0x0200: ECX = (ECX & 0xffff0000u) | (rm_vec[bx & 0xff] >> 16); EDX = (EDX & 0xffff0000u) | (rm_vec[bx & 0xff] & 0xffff); ok(); return;
    case 0x0201: rm_vec[bx & 0xff] = ((ECX & 0xffff) << 16) | (EDX & 0xffff); ok(); return;
    case 0x0202: case 0x0203: ok(); return;
    case 0x0204: ECX = (ECX & 0xffff0000u) | SEL_CODE; EDX = pm_vec[bx & 0xff]; ok(); return;
    case 0x0205: pm_vec[bx & 0xff] = EDX; LOG("set PM vector %02x -> %08x\n", bx & 0xff, EDX); ok(); return;
    case 0x0300: rm_int(bx & 0xff, SB[0] + EDI); ok(); return;
    case 0x0301: case 0x0302: LOG("DPMI call RM proc ignored\n"); ok(); return;
    case 0x0303: SETAX(0); ECX &= 0xffff0000u; EDX &= 0xffff0000u; ok(); return;
    case 0x0304: ok(); return;
    case 0x0400: SETAX(0x0009); EBX = (EBX & 0xffff0000u) | 0x0005; ECX = (ECX & 0xffff0000u) | 4; EDX = (EDX & 0xffff0000u) | 0x0870; ok(); return;
    case 0x0500: { uint32_t a = SB[0] + EDI; uint32_t fr = MEM_SIZE - heap_brk;
                   for (int k = 0; k < 0x30; k += 4) WR32(a + k, 0xffffffffu);
                   WR32(a, fr); WR32(a + 4, fr >> 12); WR32(a + 8, fr >> 12); WR32(a + 0x14, fr >> 12); WR32(a + 0x18, MEM_SIZE >> 12); WR32(a + 0x20, fr >> 12);
                   ok(); return; }
    case 0x0501: {
        uint32_t sz = ((EBX & 0xffff) << 16) | (ECX & 0xffff);
        uint32_t lin = (heap_brk + 0xfff) & ~0xfffu;
        if (lin + sz > MEM_SIZE) { err(0x8013); return; }
        heap_brk = lin + sz;
        EBX = (EBX & 0xffff0000u) | (lin >> 16); ECX = (ECX & 0xffff0000u) | (lin & 0xffff);
        ESI = (ESI & 0xffff0000u) | (lin >> 16); EDI = (EDI & 0xffff0000u) | (lin & 0xffff);
        LOG("DPMI alloc %x at %x\n", sz, lin); ok(); return;
    }
    case 0x0502: ok(); return;
    case 0x0503: {   // resize: allocate new block and copy (handle = linear address)
        uint32_t sz = ((EBX & 0xffff) << 16) | (ECX & 0xffff);
        uint32_t old = ((ESI & 0xffff) << 16) | (EDI & 0xffff);
        uint32_t lin = (heap_brk + 0xfff) & ~0xfffu; heap_brk = lin + sz;
        memmove(MEM + lin, MEM + old, sz);
        EBX = (EBX & 0xffff0000u) | (lin >> 16); ECX = (ECX & 0xffff0000u) | (lin & 0xffff);
        ESI = (ESI & 0xffff0000u) | (lin >> 16); EDI = (EDI & 0xffff0000u) | (lin & 0xffff); ok(); return;
    }
    case 0x0600: case 0x0601: case 0x0602: case 0x0603: ok(); return;
    case 0x0604: EBX &= 0xffff0000u; ECX = (ECX & 0xffff0000u) | 0x1000; ok(); return;
    case 0x0800: ok(); return;   // physical == linear for the first MB
    case 0x0801: ok(); return;
    case 0x0900: SETAL(IF); IF = 0; ok(); return;
    case 0x0901: SETAL(IF); IF = 1; ok(); return;
    case 0x0902: SETAL(IF); ok(); return;
    case 0x0a00: err(0x8001); return;
    case 0x0e00: SETAX(0x4d); ok(); return;
    case 0x0e01: ok(); return;
    }
    rt_fatal("DPMI %04x not implemented", ax);
}

// ================================================================ int dispatch
void rt_int(int n) {
    switch (n) {
    case 0x21: dos_int21(); return;
    case 0x31: dpmi(); return;
    case 0x10: int10(&EAX, &EBX, &ECX, &EDX); return;
    case 0x33: int33(&EAX, &EBX, &ECX, &EDX); return;
    case 0x2f:
        if ((EAX & 0xffff) == 0x1600) { SETAL(0); return; }   // no Windows
        if ((EAX & 0xffff) == 0x1686) { SETAX(0); return; }   // in protected mode
        if ((EAX & 0xffff) == 0x1500 || (EAX & 0xffff) == 0x150b || (EAX & 0xffff) == 0x150c) { cd_int2f(&EAX, &EBX, &ECX, &EDX, 0); return; }
        LOG("int2f %04x\n", EAX & 0xffff); return;
    case 0x16: {
        // BIOS keyboard via our scancode queue
        if (AH == 0x01 || AH == 0x11) {          // key available?
            if (kbq_r == kbq_w) { set_zf(1); return; }
            set_zf(0);
            // peek
            uint8_t sc = kbq[kbq_r];
            // rough ASCII/AX for common keys
            if (sc == 0x1c) SETAX(0x1c0d);       // Enter
            else if (sc == 0x01) SETAX(0x011b);  // Esc
            else if (sc == 0x15) SETAX(0x1579);  // Y
            else if (sc == 0x31) SETAX(0x316e);  // N
            else SETAX((uint16_t)sc << 8);
            return;
        }
        if (AH == 0x00 || AH == 0x10) {          // blocking read
            // if empty, just return "no useful key" for now (non-blocking fallback)
            if (kbq_r == kbq_w) { SETAX(0); return; }
            uint8_t sc = kbq[kbq_r];
            kbq_r = (kbq_r + 1) & (KBQ - 1);
            kb_last = sc;
            if (sc == 0x1c) SETAX(0x1c0d);
            else if (sc == 0x01) SETAX(0x011b);
            else if (sc == 0x15) SETAX(0x1579);  // Y
            else if (sc == 0x31) SETAX(0x316e);  // N
            else SETAX((uint16_t)sc << 8);
            return;
        }
        if (AH == 0x02) { SETAL(0); return; }    // shift flags
        return;
    }
    case 0x1a: { uint32_t t = RD32(0x46c); ECX = (ECX & 0xffff0000u) | (t >> 16); EDX = (EDX & 0xffff0000u) | (t & 0xffff); SETAL(0); return; }
    case 0x03: case 0x01: return;
    }
    if (pm_vec[n] && pm_vec[n] < MAGIC_BASE) {   // software int into a guest handler
        rt_deliver_int(pm_vec[n]);
        return;
    }
    rt_fatal("int %02xh not implemented (eax=%08x)", n, EAX);
}

// default handlers / magic return addresses
void sys_magic(uint32_t a) {
    if (a >= MAGIC_VEC(0) && a < MAGIC_VEC(256)) {
        int vec = (a - MAGIC_VEC(0)) >> 4;
        if (vec == 8) { /* BIOS tick */ }
        rt_iret();
        return;
    }
    rt_fatal("magic address %08x reached", a);
}
void sys_obj2_call(uint32_t off) {
    LOG("16-bit joystick helper @%x (no joystick)\n", off);
    SETAX(0);
    set_cf(1);
}

// ================================================================ host frontend
static double last_present, last_tick_t;
static double t_start;
static int headless;
static int frame_count;
static const char *dump_dir;
static int max_frames;
#ifdef USE_SDL
static SDL_Window *win; static SDL_Renderer *ren; static SDL_Texture *tex;
static uint8_t sdl_to_set1(SDL_Scancode s) {
    switch (s) {
    case SDL_SCANCODE_ESCAPE: return 0x01; case SDL_SCANCODE_1: return 0x02; case SDL_SCANCODE_2: return 0x03;
    case SDL_SCANCODE_3: return 0x04; case SDL_SCANCODE_4: return 0x05; case SDL_SCANCODE_5: return 0x06;
    case SDL_SCANCODE_6: return 0x07; case SDL_SCANCODE_7: return 0x08; case SDL_SCANCODE_8: return 0x09;
    case SDL_SCANCODE_9: return 0x0a; case SDL_SCANCODE_0: return 0x0b; case SDL_SCANCODE_MINUS: return 0x0c;
    case SDL_SCANCODE_EQUALS: return 0x0d; case SDL_SCANCODE_BACKSPACE: return 0x0e; case SDL_SCANCODE_TAB: return 0x0f;
    case SDL_SCANCODE_Q: return 0x10; case SDL_SCANCODE_W: return 0x11; case SDL_SCANCODE_E: return 0x12;
    case SDL_SCANCODE_R: return 0x13; case SDL_SCANCODE_T: return 0x14; case SDL_SCANCODE_Y: return 0x15;
    case SDL_SCANCODE_U: return 0x16; case SDL_SCANCODE_I: return 0x17; case SDL_SCANCODE_O: return 0x18;
    case SDL_SCANCODE_P: return 0x19; case SDL_SCANCODE_RETURN: return 0x1c; case SDL_SCANCODE_LCTRL: return 0x1d;
    case SDL_SCANCODE_A: return 0x1e; case SDL_SCANCODE_S: return 0x1f; case SDL_SCANCODE_D: return 0x20;
    case SDL_SCANCODE_F: return 0x21; case SDL_SCANCODE_G: return 0x22; case SDL_SCANCODE_H: return 0x23;
    case SDL_SCANCODE_J: return 0x24; case SDL_SCANCODE_K: return 0x25; case SDL_SCANCODE_L: return 0x26;
    case SDL_SCANCODE_LSHIFT: return 0x2a; case SDL_SCANCODE_Z: return 0x2c; case SDL_SCANCODE_X: return 0x2d;
    case SDL_SCANCODE_C: return 0x2e; case SDL_SCANCODE_V: return 0x2f; case SDL_SCANCODE_B: return 0x30;
    case SDL_SCANCODE_N: return 0x31; case SDL_SCANCODE_M: return 0x32; case SDL_SCANCODE_RSHIFT: return 0x36;
    case SDL_SCANCODE_LALT: return 0x38; case SDL_SCANCODE_SPACE: return 0x39;
    case SDL_SCANCODE_F1: return 0x3b; case SDL_SCANCODE_F2: return 0x3c; case SDL_SCANCODE_F3: return 0x3d;
    case SDL_SCANCODE_F4: return 0x3e; case SDL_SCANCODE_F5: return 0x3f; case SDL_SCANCODE_F6: return 0x40;
    case SDL_SCANCODE_F7: return 0x41; case SDL_SCANCODE_F8: return 0x42; case SDL_SCANCODE_F9: return 0x43;
    case SDL_SCANCODE_F10: return 0x44;
    case SDL_SCANCODE_UP: return 0x48; case SDL_SCANCODE_LEFT: return 0x4b; case SDL_SCANCODE_RIGHT: return 0x4d;
    case SDL_SCANCODE_DOWN: return 0x50; case SDL_SCANCODE_RCTRL: return 0x1d; case SDL_SCANCODE_RALT: return 0x38;
    default: return 0;
    }
}
#endif

// scripted input for headless runs: QUAR_KEYS="ms:sc,ms:sc,..."  (sc with 0x80 = release)
static struct { double t; uint8_t sc; } keyscript[256]; static int nkeys, keypos;

static void present(void) {
    vga_render();
    if (pad_on) pad_poll();
    frame_count++;
    if (verbose && frame_count % 70 == 0) {
        int pal = 0, nz = 0; for (int i = 0; i < 256; i++) pal += dac[i][0] + dac[i][1] + dac[i][2];
        for (int p = 0; p < 4; p++) for (int k = 0; k < 65536; k++) nz += planes[p][k] != 0;
        fprintf(stderr, "[frame %d] flips %llu, vga writes %llu, palette sum %d, nonzero plane bytes %d, start %02x%02x seq4 %02x mask %02x gc5 %02x crtc13 %02x 14 %02x 17 %02x 09 %02x\n",
                frame_count, (unsigned long long)flip_count, (unsigned long long)vga_wcount, pal, nz, crtc[0x0c], crtc[0x0d], seq[4], seq[2], gc[5], crtc[0x13], crtc[0x14], crtc[0x17], crtc[0x09]);
    }
    if (watch_addr && frame_count % 35 == 0)   // QUAR_WATCH=hexaddr: log a guest dword twice a second
        fprintf(stderr, "[watch %.2fs] %08x = %d\n", now_s() - t_start, watch_addr, (int32_t)RD32(watch_addr));
    if (dump_dir && (frame_count % 35 == 0)) {
        char p[1024]; snprintf(p, sizeof p, "%s/frame_%05d.ppm", dump_dir, frame_count);
        FILE *f = fopen(p, "wb");
        if (f) { fprintf(f, "P6 320 %d 255\n", scr_h);
                 for (int k = 0; k < 320 * scr_h; k++) { uint32_t c = framebuf[k]; fputc(c >> 16, f); fputc(c >> 8, f); fputc(c, f); }
                 fclose(f); }
    }
    if (dump_dir && getenv("QUAR_VRAMDUMP") && frame_count == atoi(getenv("QUAR_VRAMDUMP"))) {
        char p[1024]; snprintf(p, sizeof p, "%s/vram_%05d.ppm", dump_dir, frame_count);
        FILE *f = fopen(p, "wb");
        if (f) { fprintf(f, "P6 320 819 255\n");
                 for (int k = 0; k < 320 * 819; k++) { int y = k / 320, x = k % 320; uint8_t c = planes[x & 3][(y * 80 + (x >> 2)) & 0xffff];
                     fputc(dac[c][0] << 2, f); fputc(dac[c][1] << 2, f); fputc(dac[c][2] << 2, f); }
                 fclose(f); }
        { int hist[256] = {0}; for (int p = 0; p < 4; p++) for (int k = 0; k < 65536; k++) hist[planes[p][k]]++;
          fprintf(stderr, "vram colors:"); for (int i = 1; i < 256; i++) if (hist[i]) fprintf(stderr, " %d:%d", i, hist[i]); fprintf(stderr, "\n"); }
        fprintf(stderr, "palette:"); for (int i = 0; i < 256; i++) if (dac[i][0] | dac[i][1] | dac[i][2]) fprintf(stderr, " %d=%02x%02x%02x", i, dac[i][0], dac[i][1], dac[i][2]); fprintf(stderr, "\n");
    }
    if (max_frames && frame_count >= max_frames) { fprintf(stderr, "[max frames reached]\n"); sys_shutdown(); exit(0); }
#ifdef USE_SDL
    if (!headless) {
        SDL_Event e;
        while (SDL_PollEvent(&e)) {
            if (e.type == SDL_EVENT_QUIT) { sys_shutdown(); exit(0); }
            if (e.type == SDL_EVENT_KEY_DOWN || e.type == SDL_EVENT_KEY_UP) {
                if (e.key.repeat) continue;
                if (e.key.scancode == SDL_SCANCODE_F11) {     // F11: toggle fullscreen (not passed to the game)
                    if (e.type == SDL_EVENT_KEY_DOWN) { cfg.fullscreen ^= 1; SDL_SetWindowFullscreen(win, cfg.fullscreen); cfg_save(); }
                    continue;
                }
                if (e.key.scancode == SDL_SCANCODE_F10) {     // F10: next output filter
                    if (e.type == SDL_EVENT_KEY_DOWN) { cfg.filter = (cfg.filter + 1) % FILTER_COUNT; cfg_save(); }
                    continue;
                }
                uint8_t sc = sdl_to_set1(e.key.scancode);
                int ext = e.key.scancode == SDL_SCANCODE_UP || e.key.scancode == SDL_SCANCODE_DOWN ||
                          e.key.scancode == SDL_SCANCODE_LEFT || e.key.scancode == SDL_SCANCODE_RIGHT ||
                          e.key.scancode == SDL_SCANCODE_RCTRL || e.key.scancode == SDL_SCANCODE_RALT;
                if (sc) { if (ext) kb_push(0xe0); kb_push(sc | (e.type == SDL_EVENT_KEY_UP ? 0x80 : 0)); }
            }
        }
        static int lh = -1;
        int h = cfg.square ? scr_h * 4 : 960;             // 4:3 like a CRT, or square pixels
        if (h != lh) { SDL_SetRenderLogicalPresentation(ren, 1280, h, SDL_LOGICAL_PRESENTATION_LETTERBOX); lh = h; }
        SDL_RenderClear(ren);
        filter_draw(ren, tex, framebuf, SCR_W, scr_h);
        static int shot_at = -1; static const char *shot_path;   // QUAR_SHOT="frame:file.bmp": save the window
        if (shot_at == -1) { const char *e = getenv("QUAR_SHOT"); shot_at = e ? atoi(e) : 0; shot_path = e && strchr(e, ':') ? strchr(e, ':') + 1 : 0; }
        if (shot_path && frame_count == shot_at) {
            SDL_Surface *sf = SDL_RenderReadPixels(ren, NULL);
            if (sf) { SDL_SaveBMP(sf, shot_path); SDL_DestroySurface(sf); }
        }
        SDL_RenderPresent(ren);
    }
#endif
}

void sys_host_tick(void) {
    double t = now_s();
    // timer IRQs owed at the programmed PIT rate (cap the backlog)
    double dt = t - last_tick_t;
    double rate = pit_rate();
    int n = (int)(dt * rate);
    if (n > 0) {
        last_tick_t += n / rate;
        if (pm_vec[8]) { timer_ticks_owed += n; if (timer_ticks_owed > 8) timer_ticks_owed = 8; }
        bios_tick_acc += n / rate * 18.2065;
        while (bios_tick_acc >= 1) { WR32(0x46c, RD32(0x46c) + 1); bios_tick_acc -= 1; }
    }
    while (keypos < nkeys && t - t_start >= keyscript[keypos].t) { kb_push(keyscript[keypos].sc); keypos++; }
    if (t - last_present >= 1.0 / 70) { last_present = t; present(); }
}

static void *timer_thread(void *arg) {
    (void)arg;
    for (;;) { host_sleep_ns(1000000); irq_pending = 1; }
    return 0;
}

void sys_fatal_box(const char *msg) {
#ifdef USE_SDL
    if (!headless) SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_ERROR, "Quarantine", msg, win);
#else
    (void)msg;
#endif
}

void sys_shutdown(void) {
    snd_shutdown();
    cd_stats();
#ifdef USE_SDL
    if (win) SDL_Quit();
#endif
}

void sys_init(int argc, char **argv) {
    (void)argc; (void)argv;
    verbose = getenv("QUAR_VERBOSE") != 0;
    headless = getenv("QUAR_HEADLESS") != 0;
    if (getenv("QUAR_WATCH")) watch_addr = (uint32_t)strtoul(getenv("QUAR_WATCH"), 0, 16);
    dump_dir = getenv("QUAR_DUMP");
    if (getenv("QUAR_MAXFRAMES")) max_frames = atoi(getenv("QUAR_MAXFRAMES"));
    if (getenv("QUAR_KEYS")) {
        char *s = strdup(getenv("QUAR_KEYS")), *tok;
        for (tok = strtok(s, ","); tok && nkeys < 256; tok = strtok(0, ",")) {
            unsigned ms, sc; if (sscanf(tok, "%u:%x", &ms, &sc) == 2) { keyscript[nkeys].t = ms / 1000.0; keyscript[nkeys].sc = sc; nkeys++; }
        }
    }
    for (int k = 0; k < 64; k++) dos_fd[k] = -1;
    dos_fd[0] = 0; dos_fd[1] = 1; dos_fd[2] = 2;

    // descriptors
    def_sel(SEL_CODE, 0, 0xffffffffu, 0x9a);
    def_sel(SEL_DATA, 0, 0xffffffffu, 0x92);
    def_sel(SEL_PSP, PSP_LIN, 0xff, 0x92);
    def_sel(SEL_ENV, ENV_LIN, 0xfff, 0x92);
    for (int v = 0; v < 256; v++) pm_vec[v] = MAGIC_VEC(v);

    // PSP: command tail, env selector, DOS/4GW extension (+0x5c = top of program memory)
    WR16(PSP_LIN, 0x20cd);
    WR16(PSP_LIN + 0x2c, SEL_ENV);
    WR32(PSP_LIN + 0x5c, OBJ3_BASE + 0x30000);
    WR8(PSP_LIN + 0x80, 0); WR8(PSP_LIN + 0x81, 0x0d);
    const char *env[] = {"COMSPEC=C:\\COMMAND.COM", "PATH=C:\\", "BLASTER=", 0};
    uint32_t p = ENV_LIN;
    for (int k = 0; env[k]; k++) { if (!env[k][8] && !strcmp(env[k], "BLASTER=")) continue; for (const char *c = env[k]; *c; c++) WR8(p++, *c); WR8(p++, 0); }
    WR8(p++, 0); WR16(p, 1); p += 2;
    for (const char *c = "C:\\QUARAN\\SKIPIT.EXE"; *c; c++) WR8(p++, *c);
    WR8(p++, 0);

    set_sreg(1, SEL_CODE);
    set_sreg(2, SEL_DATA); set_sreg(3, SEL_DATA); set_sreg(0, SEL_PSP);
    set_sreg(4, 0); set_sreg(5, 0);
    vga_set_mode(3);
    retrace_t0 = t_start = last_present = last_tick_t = now_s();

    // ---- configuration (config.ini in the per-user folder; environment variables override it)
    cfg_load();
    if (getenv("QUAR_COPYPROT")) cfg.copyprot = atoi(getenv("QUAR_COPYPROT")) != 0;
    if (getenv("QUAR_NOVSYNC")) cfg.framecap = 0;
    int want_launcher = 0;
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "--launcher") || !strcmp(argv[i], "--config")) want_launcher = 1;

#ifdef USE_SDL
    if (!headless) {
        if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_GAMEPAD)) rt_fatal("SDL_Init: %s", SDL_GetError());
        win = SDL_CreateWindow("Quarantine", 1280, 960, SDL_WINDOW_RESIZABLE | SDL_WINDOW_HIGH_PIXEL_DENSITY | (cfg.fullscreen ? SDL_WINDOW_FULLSCREEN : 0));
        ren = SDL_CreateRenderer(win, NULL);
        SDL_SetRenderVSync(ren, 1);
        tex = SDL_CreateTexture(ren, SDL_PIXELFORMAT_XRGB8888, SDL_TEXTUREACCESS_STREAMING, 320, 240);
        SDL_PumpEvents();
        const bool *ks = SDL_GetKeyboardState(NULL);
        if (ks[SDL_SCANCODE_LSHIFT] || ks[SDL_SCANCODE_RSHIFT]) want_launcher = 1;   // hold Shift to get the launcher
    }
#endif

    // ---- game source: disc image (installed to <config>/data) or an extracted folder
    char err[512] = "";
    if (getenv("QUAR_DATA")) {                       // development override: use these files as they are
        snprintf(data_dir, sizeof data_dir, "%s", getenv("QUAR_DATA"));
        disc_open(getenv("QUAR_CDAUDIO") ? getenv("QUAR_CDAUDIO") : "extracted", err, sizeof err);   // music only
    } else {
        if (!cfg.disc[0] && access("extracted/cd/SKIPIT.EXE", R_OK) == 0) {   // repository checkout with extract.py output
            char abs[1024]; if (realpath("extracted", abs)) snprintf(cfg.disc, sizeof cfg.disc, "%s", abs);
        }
        int ok = disc_open(cfg.disc, err, sizeof err) == 0;
#ifdef USE_SDL
        if (!headless && (cfg.launcher || !ok || want_launcher)) {
            if (!launcher_run(win, ren, err)) { sys_shutdown(); exit(0); }
            ok = 1;
        }
#endif
        if (!ok) rt_fatal("%s\n(start the game without QUAR_HEADLESS to choose a disc image)", err[0] ? err : "no disc image configured");
        char dest[1100]; snprintf(dest, sizeof dest, "%sdata", cfg_dir());
        if (disc_kind() == SRC_IMAGE) {
            if (disc_install(dest, 0, 0, err, sizeof err)) rt_fatal("installing the game files: %s", err);
            snprintf(data_dir, sizeof data_dir, "%s", dest);
        } else snprintf(data_dir, sizeof data_dir, "%s", disc_data_dir());
    }
    if (getenv("QUAR_SAVE")) snprintf(save_dir, sizeof save_dir, "%s", getenv("QUAR_SAVE"));
    else snprintf(save_dir, sizeof save_dir, "%ssave", cfg_dir());
    mkdir(save_dir, 0755);
    no_vsync = !cfg.framecap;
    rt_skip_copyprot = !cfg.copyprot;
    LOG("data %s, saves %s, config %s\n", data_dir, save_dir, cfg_dir());
    guest_load_exe(data_dir);      // the program itself comes from the player's copy of the game

#ifdef USE_SDL
    if (!headless) {
        SDL_SetRenderScale(ren, 1, 1);
    }
#endif
    {
        static cd_track_src tracks[98];
        int n = disc_audio_tracks(tracks, 98);
        cd_init_tracks(tracks, n, disc_data_sectors());
        if (!n) LOG("no CD music available: tracks will be silent\n");
    }
    cd_audio_start(headless);
    cd_set_volume(cfg.music);
    // The CD ships SOUND.DAT = 0 (no card); SETUP.EXE would write a device id. Any non-zero id selects
    // the emulated SOS driver (rt_snd.c). A SOUND.DAT already in the save directory wins.
    {
        char p[1100]; snprintf(p, sizeof p, "%s/SOUND.DAT", save_dir);
        if (access(p, F_OK) != 0) { FILE *f = fopen(p, "wb"); if (f) { fputc(0x16, f); fputc(0xe0, f); fclose(f); } }
    }
    snd_init();
    snd_start(headless);
    snd_set_volume(cfg.sfx);
    if (!headless || getenv("QUAR_PADTEST")) { pad_init(); pad_on = 1; }
    pthread_t th; pthread_create(&th, 0, timer_thread, 0);
}
