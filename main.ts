// Tiny stack VM for make.fun's tiny stack ISA v1. One run answers all 40
// instances of a set. Deterministic: no clock, no randomness.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const STACK_MAX = 256, CALL_MAX = 64, MEM_WORDS = 256;
const STEP_LIMIT = 1_000_000, OUT_MAX = 65_536;

// Per opcode: immediate bytes, values popped, values pushed. IMM 255 = no opcode.
const IMM = new Uint8Array(256).fill(255);
const POPS = new Uint8Array(256);
const PUSHES = new Uint8Array(256);
for (const [op, imm, pops, pushes] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
]) { IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes; }

/** Runs one program on one input: the bytes it wrote and its exit code. */
export function runVM(program: Uint8Array, input: Uint8Array): { stdout: Uint8Array; exit: number } {
  const n = program.length;
  const stack = new Int32Array(STACK_MAX);
  let sp = 0;
  const calls = new Int32Array(CALL_MAX);
  let cp = 0;
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_MAX);
  let olen = 0, inPos = 0, pc = 0, steps = 0;
  const done = (exit: number) => ({ stdout: out.subarray(0, olen), exit });

  for (;;) {
    // Checks in the ISA's order: step limit, pc, opcode, immediate.
    if (steps === STEP_LIMIT) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = program[pc];
    const imm = IMM[op];
    if (imm === 255) return done(5);
    if (pc + imm >= n) return done(9);
    steps++;
    const pops = POPS[op], pushes = PUSHES[op];
    if (sp < pops) return done(2);
    if (sp - pops + pushes > STACK_MAX) return done(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: stack[sp++] = (program[nx - 1] << 24) >> 24; break;
      case 0x02:
        stack[sp++] = program[nx - 4] | (program[nx - 3] << 8) | (program[nx - 2] << 16) | (program[nx - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break;
      case 0x05: { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; break; }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break;
      case 0x07: {
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = (-stack[sp - 1]) | 0; break;
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1], a = stack[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
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
        stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[nx - 2] | (program[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30) { pc = nx + rel; break; }
        const v = stack[--sp];
        if (op === 0x31 ? v === 0 : v !== 0) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === CALL_MAX) return done(7);
        calls[cp++] = nx;
        pc = program[nx - 2] | (program[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1], v = stack[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(stack[sp - 1]);
        if (olen + s.length > OUT_MAX) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return done(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52:
        stack[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53:
        return done(stack[--sp] & 255);
    }
  }
}

function main(): void {
  for (let i = 1; i <= 40; i++) {
    const id = `i${String(i).padStart(3, '0')}`;
    const outDir = join(OUTPUT_DIR, id);
    mkdirSync(outDir, { recursive: true });
    let program: Buffer, input: Buffer;
    try {
      program = readFileSync(join(INPUT_DIR, id, 'program.bin'));
      input = readFileSync(join(INPUT_DIR, id, 'input.bin'));
    } catch {
      writeFileSync(join(outDir, 'stdout.bin'), new Uint8Array(0));
      writeFileSync(join(outDir, 'exit.txt'), '0\n');
      continue;
    }
    const { stdout, exit } = runVM(program, input);
    writeFileSync(join(outDir, 'stdout.bin'), stdout);
    writeFileSync(join(outDir, 'exit.txt'), `${exit}\n`);
  }
}

// Driver runs only when this file is the entry point.
if ((process.argv[1] ?? '').endsWith('main.ts')) main();
