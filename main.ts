// Tiny stack VM: faithful interpreter of the tiny stack ISA.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(p, inp) {
  const n = p.length;
  // Pre-decode: OP=opcode (255 unknown, 254 immediate cut off), AR=immediate, NX=next pc.
  const OP = new Uint8Array(n), AR = new Int32Array(n), NX = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const b = p[i];
    if (b > 0x53 || (b > 7 && b < 0x10) || (b > 0x22 && b < 0x30) || (b > 0x34 && b < 0x40) || (b > 0x41 && b < 0x50)) { OP[i] = 255; continue; }
    const m = b === 1 || b === 2 ? (b === 1 ? 1 : 4) : b >= 0x30 && b <= 0x33 ? 2 : 0;
    if (i + m >= n) { OP[i] = 254; continue; }
    OP[i] = b;
    NX[i] = i + 1 + m;
    if (b === 1) AR[i] = (p[i + 1] << 24) >> 24;
    else if (b === 2) AR[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (b >= 0x30 && b <= 0x32) AR[i] = ((p[i + 1] | (p[i + 2] << 8)) << 16) >> 16;
    else if (b === 0x33) AR[i] = p[i + 1] | (p[i + 2] << 8);
  }
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const o = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (c) => [o.subarray(0, ol), c];
  for (;;) {
    if (st === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const b = OP[pc];
    if (b === 255) return end(5);
    if (b === 254) return end(9);
    st++;
    const nx = NX[pc], arg = AR[pc];
    switch (b) {
      case 0x00:
        return end(0);
      case 0x01: case 0x02:
        if (sp >= 256) return end(3);
        D[sp++] = arg;
        pc = nx;
        break;
      case 0x03:
        if (sp < 1) return end(2);
        sp--;
        pc = nx;
        break;
      case 0x04:
        if (sp < 1) return end(2);
        if (sp >= 256) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        pc = nx;
        break;
      case 0x05:
        if (sp < 2) return end(2);
        { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; }
        pc = nx;
        break;
      case 0x06:
        if (sp < 2) return end(2);
        if (sp >= 256) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        pc = nx;
        break;
      case 0x07:
        if (sp < 3) return end(2);
        { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; }
        pc = nx;
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return end(2);
        const y = D[sp - 1], x = D[sp - 2];
        let r;
        if (b === 0x10) r = (x + y) | 0;
        else if (b === 0x11) r = (x - y) | 0;
        else if (b === 0x12) r = Math.imul(x, y);
        else if (b === 0x13) { if (y === 0) return end(4); r = x === -2147483648 && y === -1 ? x : (x / y) | 0; }
        else if (b === 0x14) { if (y === 0) return end(4); r = y === -1 ? 0 : (x % y) | 0; }
        else if (b === 0x15) { if (y === 0) return end(4); r = Math.floor((x >>> 0) / (y >>> 0)) | 0; }
        else if (b === 0x16) { if (y === 0) return end(4); r = ((x >>> 0) % (y >>> 0)) | 0; }
        else if (b === 0x18) r = x & y;
        else if (b === 0x19) r = x | y;
        else if (b === 0x1a) r = x ^ y;
        else if (b === 0x1c) r = x << (y & 31);
        else if (b === 0x1d) r = x >> (y & 31);
        else if (b === 0x1e) r = (x >>> (y & 31)) | 0;
        else if (b === 0x20) r = x === y ? 1 : 0;
        else if (b === 0x21) r = x < y ? 1 : 0;
        else r = (x >>> 0) < (y >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        pc = nx;
        break;
      }
      case 0x17:
        if (sp < 1) return end(2);
        D[sp - 1] = (-D[sp - 1]) | 0;
        pc = nx;
        break;
      case 0x1b:
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1];
        pc = nx;
        break;
      case 0x30: case 0x31: case 0x32: {
        let t = 1;
        if (b !== 0x30) {
          if (sp < 1) return end(2);
          const v = D[--sp];
          t = b === 0x31 ? v === 0 : v !== 0;
        }
        pc = t ? nx + arg : nx;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = arg;
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40:
        if (sp < 1) return end(2);
        { const a = D[sp - 1]; if (a < 0 || a >= 256) return end(6); D[sp - 1] = M[a]; }
        pc = nx;
        break;
      case 0x41:
        if (sp < 2) return end(2);
        { const a = D[sp - 1], v = D[sp - 2]; if (a < 0 || a >= 256) return end(6); sp -= 2; M[a] = v; }
        pc = nx;
        break;
      case 0x50:
        if (sp < 1) return end(2);
        { const s = String(D[sp - 1]); if (ol + s.length > 65536) return end(11); sp--; for (let i = 0; i < s.length; i++) o[ol++] = s.charCodeAt(i); }
        pc = nx;
        break;
      case 0x51:
        if (sp < 1) return end(2);
        if (ol + 1 > 65536) return end(11);
        o[ol++] = D[--sp] & 255;
        pc = nx;
        break;
      case 0x52:
        if (sp >= 256) return end(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc = nx;
        break;
      case 0x53:
        if (sp < 1) return end(2);
        return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, code] = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
