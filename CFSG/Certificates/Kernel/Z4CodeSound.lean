module

public import Certificates.Data.Kernel.Z4Code
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZData
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Z4Code

open CFSG.OddStandard.AltStdSmall4.G2 CFSG.OddStandard.AltStdSmall4.G2.Z4M

theorem ofCode_mk {y0 y1 y2 s a b c : Nat} (h0 : y0 < 4) (h1 : y1 < 4) (h2 : y2 < 4) (hs : s < 2)
    (ha : a < 2) (hb : b < 2) (hc : c < 2) :
    ofCode (y0 + 4 * y1 + 16 * y2 + 64 * s + 128 * a + 256 * b + 512 * c) =
      ⟨(y0 : ZMod 4), (y1 : ZMod 4), (y2 : ZMod 4), (s : ZMod 2), (a : ZMod 2), (b : ZMod 2),
        (c : ZMod 2)⟩ := by
  simp only [ofCode, Z4M.mk.injEq]
  refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_,
    congrArg _ ?_, congrArg _ ?_⟩ <;> omega

theorem three_eq : (3 : ZMod 4) = -1 := by decide

theorem mul_eq (p q : Z4M) : p * q =
    let M := dEnt p.a p.b p.c
    let w := uS p.s
    ⟨p.x0 + w * (M.e00 * q.x0 + M.e01 * q.x1 + M.e02 * q.x2),
      p.x1 + w * (M.e10 * q.x0 + M.e11 * q.x1 + M.e12 * q.x2),
      p.x2 + w * (M.e20 * q.x0 + M.e21 * q.x1 + M.e22 * q.x2),
      p.s + q.s, p.a + q.a, p.b + q.b + p.a * q.c, p.c + q.c⟩ := rfl

theorem ofCode_mulC (m n : Nat) : ofCode (mulC m n) = ofCode m * ofCode n := by
  rw [mulC, ofCode_mk (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), mul_eq]
  simp only [ofCode, Z4M.mk.injEq]
  rcases Nat.mod_two_eq_zero_or_one (m / 64) with hs | hs <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 128) with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 256) with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 512) with hc | hc <;>
  simp only [hs, ha, hb, hc, Nat.cast_zero, Nat.cast_one, dEnt, uS, dE, DT, if_pos,
    one_ne_zero, if_false, if_true, Nat.reduceMul, Nat.reduceAdd, Nat.reduceShiftRight,
    Nat.reduceAnd, Nat.cast_zero, zero_mul, one_mul, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    three_eq] <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

theorem code_lt {y0 y1 y2 s a b c : Nat} (h0 : y0 < 4) (h1 : y1 < 4) (h2 : y2 < 4) (hs : s < 2)
    (ha : a < 2) (hb : b < 2) (hc : c < 2) :
    y0 + 4 * y1 + 16 * y2 + 64 * s + 128 * a + 256 * b + 512 * c < 1024 := by
  omega

theorem mulC_lt (m n : Nat) : mulC m n < 1024 :=
  code_lt (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))

theorem ofCode_inj {m n : Nat} (hm : m < 1024) (hn : n < 1024) (h : ofCode m = ofCode n) :
    m = n := by
  rw [← toCode_ofCode hm, h, toCode_ofCode hn]

theorem ofCode_zero : ofCode 0 = 1 := by
  ext <;> rfl

theorem z2_beq {d : Nat} (hd : d < 2) : (((d : ℕ) : ZMod 2) == 0) = Nat.beq d 0 := by
  interval_cases d <;> rfl

theorem z4_two {d : Nat} (hd : d < 4) : (2 * ((d : ℕ) : ZMod 4) == 0) = e4 d := by
  interval_cases d <;> rfl

theorem inM_eq (x : Nat) : inM (ofCode x) = inM4c x :=
  z2_beq (Nat.mod_lt _ (by omega))

theorem inA_eq (x : Nat) : inA (ofCode x) = inA4c x := by
  unfold inA inA4c
  rw [← z2_beq (Nat.mod_lt (x / 64) (by omega)), ← z2_beq (Nat.mod_lt (x / 128) (by omega)),
    ← z2_beq (Nat.mod_lt (x / 256) (by omega)), ← z2_beq (Nat.mod_lt (x / 512) (by omega))]
  rfl

theorem inE_eq (x : Nat) : inE (ofCode x) = inE4c x := by
  unfold inE inE4c
  rw [inA_eq, ← z4_two (Nat.mod_lt x (by omega)), ← z4_two (Nat.mod_lt (x / 4) (by omega)),
    ← z4_two (Nat.mod_lt (x / 16) (by omega))]
  rfl

theorem tm_eq : tm = ofCode 64 := by
  ext <;> rfl

section Z8

variable {u : (ZMod 8)ˣ}

theorem ofCode8_mk {y0 y1 y2 s a b c : Nat} (h0 : y0 < 8) (h1 : y1 < 8) (h2 : y2 < 8)
    (hs : s < 2) (ha : a < 2) (hb : b < 2) (hc : c < 2) :
    Z8M.ofCode u (y0 + 8 * y1 + 64 * y2 + 512 * s + 1024 * a + 2048 * b + 4096 * c) =
      ⟨(y0 : ZMod 8), (y1 : ZMod 8), (y2 : ZMod 8), (s : ZMod 2), (a : ZMod 2), (b : ZMod 2),
        (c : ZMod 2)⟩ := by
  simp only [Z8M.ofCode, Z8M.mk.injEq]
  refine ⟨congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_, congrArg _ ?_,
    congrArg _ ?_, congrArg _ ?_⟩ <;> omega

theorem mul8_eq (p q : Z8M u) : p * q =
    let M := Z8M.dEnt p.a p.b p.c
    let w := Z8M.uS u p.s
    ⟨p.x0 + w * (M.e00 * q.x0 + M.e01 * q.x1 + M.e02 * q.x2),
      p.x1 + w * (M.e10 * q.x0 + M.e11 * q.x1 + M.e12 * q.x2),
      p.x2 + w * (M.e20 * q.x0 + M.e21 * q.x1 + M.e22 * q.x2),
      p.s + q.s, p.a + q.a, p.b + q.b + p.a * q.c, p.c + q.c⟩ := rfl

theorem ofCode8_mulC8 {uv : Nat} (hu : ((uv : ℕ) : ZMod 8) = (u : ZMod 8)) (m n : Nat) :
    Z8M.ofCode u (mulC8 uv m n) = Z8M.ofCode u m * Z8M.ofCode u n := by
  rw [mulC8, ofCode8_mk (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), mul8_eq]
  simp only [Z8M.ofCode, Z8M.mk.injEq]
  rcases Nat.mod_two_eq_zero_or_one (m / 512) with hs | hs <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 1024) with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 2048) with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one (m / 4096) with hc | hc <;>
  simp only [hs, ha, hb, hc, Nat.cast_zero, Nat.cast_one, Z8M.dEnt, Z8M.uS, dE8, DT8, if_pos,
    one_ne_zero, if_false, if_true, Nat.reduceMul, Nat.reduceAdd, Nat.reduceShiftRight,
    Nat.reduceAnd, zero_mul, one_mul, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, hu, zero_ne_one, ↓reduceIte] <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

theorem code8_lt {y0 y1 y2 s a b c : Nat} (h0 : y0 < 8) (h1 : y1 < 8) (h2 : y2 < 8) (hs : s < 2)
    (ha : a < 2) (hb : b < 2) (hc : c < 2) :
    y0 + 8 * y1 + 64 * y2 + 512 * s + 1024 * a + 2048 * b + 4096 * c < 8192 := by
  omega

theorem mulC8_lt (uv m n : Nat) : mulC8 uv m n < 8192 :=
  code8_lt (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))

theorem ofCode8_inj {m n : Nat} (hm : m < 8192) (hn : n < 8192)
    (h : Z8M.ofCode u m = Z8M.ofCode u n) : m = n := by
  rw [← Z8M.toCode_ofCode (u := u) hm, h, Z8M.toCode_ofCode hn]

theorem ofCode8_zero : Z8M.ofCode u 0 = 1 := by
  ext <;> rfl

theorem inM8_eq (x : Nat) : Z8M.inM (Z8M.ofCode u x) = inM8c x :=
  z2_beq (Nat.mod_lt _ (by omega))

theorem inA8_eq (x : Nat) : Z8M.inA (Z8M.ofCode u x) = inA8c x := by
  unfold Z8M.inA inA8c
  rw [← z2_beq (Nat.mod_lt (x / 512) (by omega)), ← z2_beq (Nat.mod_lt (x / 1024) (by omega)),
    ← z2_beq (Nat.mod_lt (x / 2048) (by omega)), ← z2_beq (Nat.mod_lt (x / 4096) (by omega))]
  rfl

theorem tm8_eq : Z8M.tm u = Z8M.ofCode u 512 := by
  ext <;> rfl

end Z8

end CFSG.KC.Z4Code
