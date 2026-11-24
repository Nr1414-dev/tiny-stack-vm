// Tiny stack VM — Variant A2 ("plain, golfed"). Faithful interpreter of make.fun's
// tiny stack ISA v1. Reads /input/<id>/{program,input}.bin, writes /output/<id>/{stdout.bin,exit.txt}.
import { mkdirSync as mkdir, readdirSync as readdir, readFileSync as read, writeFileSync as write } from 'node:fs';
import { join } from 'node:path';

// Opcode table, packed: for each known opcode, 2 hex digits + 1 char.
// The char's code minus 35 is (immediate bytes << 4) | (popped << 2) | pushed.
const IMM = new Uint8Array(256);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
const S = "00#01402d03'04)05-06.07210,11,12,13,14,15,16,17(18,19,1a,1b(1c,1d,1e,20,21,22,30C31G32G33C34#40(41+50'51'52$53'";
for (let i = 0; i < S.length; i += 3) {
  const o = parseInt(S.slice(i, i + 2), 16);
  const v = S.charCodeAt(i + 2) - 35;
  IMM[o] = v >> 4;
  POP[o] = (v >> 2) & 3;
  PSH[o] = v & 3;
  KNOWN[o] = 1;
}

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const enc = new TextEncoder();
  const end = (code: number) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc];
    if (!KNOWN[op]) return end(5);
    const imm = IMM[op];
    if (pc + imm >= p.length) return end(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < POP[op]) return end(2);
    if (sp - POP[op] + PSH[op] > 256) return end(3);
    pc = next;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17:
        D[sp - 1] = (-D[sp - 1]) | 0;
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return end(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= 256) return end(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > 65536) return end(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(D[--sp] & 255);
      default:
        return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdir(I).sort()) {
  const r = run(new Uint8Array(read(join(I, id, 'program.bin'))), new Uint8Array(read(join(I, id, 'input.bin'))));
  mkdir(join(O, id), { recursive: true });
  write(join(O, id, 'stdout.bin'), r.out);
  write(join(O, id, 'exit.txt'), `${r.code}\n`);
}
