module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModFox

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix
open Certificates.A5GL42 (Mat4)

@[expose] def ofBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => (if f 0 then 1 else 0) + 2 * ofBits n fun p => f (p + 1)

theorem testBit_ofBits : ∀ (n : ℕ) (f : ℕ → Bool) (j : ℕ), j < n →
    (ofBits n f).testBit j = f j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, 0, _ => by
    rw [ofBits, Nat.testBit_zero]
    cases h : f 0
    · simp only [Bool.false_eq_true, if_false, zero_add]
      simp
    · simp only [if_true]
      simp [Nat.add_mul_mod_self_left]
  | n + 1, f, j + 1, hj => by
    rw [ofBits, Nat.testBit_succ]
    have h : ((if f 0 then 1 else 0) + 2 * ofBits n fun p => f (p + 1)) / 2 =
        ofBits n fun p => f (p + 1) := by
      split <;> omega
    rw [h, testBit_ofBits n _ j (by omega)]

@[expose] def bmat (x : ℕ) : Mat4 :=
  Matrix.of fun i j => if x.testBit (4 * (i : ℕ) + (j : ℕ)) then 1 else 0

@[expose] def codeOf (M : Mat4) : ℕ := ofBits 16 fun p =>
  decide (M (Fin.ofNat 4 (p / 4)) (Fin.ofNat 4 (p % 4)) = 1)

theorem bmat_codeOf (M : Mat4) : bmat (codeOf M) = M := by
  ext i j
  have hp : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  have h1 : (4 * (i : ℕ) + (j : ℕ)) / 4 = (i : ℕ) := by omega
  have h2 : (4 * (i : ℕ) + (j : ℕ)) % 4 = (j : ℕ) := by omega
  have key : (codeOf M).testBit (4 * (i : ℕ) + (j : ℕ)) = decide (M i j = 1) := by
    rw [codeOf, testBit_ofBits 16 _ _ hp, h1, h2, Fin.ofNat_val_eq_self, Fin.ofNat_val_eq_self]
  simp only [bmat, Matrix.of_apply, key]
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (M i j) with h | h <;> simp [h]

@[expose] def mulB (x y : ℕ) : ℕ := ofBits 16 fun p =>
  xor (xor (x.testBit (4 * (p / 4)) && y.testBit (p % 4))
           (x.testBit (4 * (p / 4) + 1) && y.testBit (4 + p % 4)))
      (xor (x.testBit (4 * (p / 4) + 2) && y.testBit (8 + p % 4))
           (x.testBit (4 * (p / 4) + 3) && y.testBit (12 + p % 4)))

private theorem bool_dot (a0 a1 a2 a3 b0 b1 b2 b3 : Bool) :
    (if xor (xor (a0 && b0) (a1 && b1)) (xor (a2 && b2) (a3 && b3)) then 1 else 0 : ZMod 2) =
      (if a0 then 1 else 0) * (if b0 then 1 else 0) + (if a1 then 1 else 0) * (if b1 then 1 else 0)
      + (if a2 then 1 else 0) * (if b2 then 1 else 0)
      + (if a3 then 1 else 0) * (if b3 then 1 else 0) := by
  revert a0 a1 a2 a3 b0 b1 b2 b3
  decide +kernel

theorem bmat_mulB (x y : ℕ) : bmat (mulB x y) = bmat x * bmat y := by
  ext i j
  have hp : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  have h1 : (4 * (i : ℕ) + (j : ℕ)) / 4 = (i : ℕ) := by omega
  have h2 : (4 * (i : ℕ) + (j : ℕ)) % 4 = (j : ℕ) := by omega
  have key : (mulB x y).testBit (4 * (i : ℕ) + (j : ℕ)) =
      xor (xor (x.testBit (4 * (i : ℕ)) && y.testBit (j : ℕ))
               (x.testBit (4 * (i : ℕ) + 1) && y.testBit (4 + (j : ℕ))))
          (xor (x.testBit (4 * (i : ℕ) + 2) && y.testBit (8 + (j : ℕ)))
               (x.testBit (4 * (i : ℕ) + 3) && y.testBit (12 + (j : ℕ)))) := by
    rw [mulB, testBit_ofBits 16 _ _ hp, h1, h2]
  have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [bmat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four, key, e0, e1, e2, e3,
    Nat.reduceMul, add_zero, mul_zero, zero_add]
  exact bool_dot _ _ _ _ _ _ _ _

theorem bmat_xor (x y : ℕ) : bmat (x ^^^ y) = bmat x + bmat y := by
  ext i j
  simp only [bmat, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  generalize x.testBit (4 * (i : ℕ) + (j : ℕ)) = a
  generalize y.testBit (4 * (i : ℕ) + (j : ℕ)) = b
  revert a b
  decide

theorem bmat_one : bmat 33825 = 1 := by
  decide +kernel

theorem bmat_zero : bmat 0 = 0 := by
  decide +kernel

@[expose] def wpairB (a b U V : ℕ) : List Bool → ℕ × ℕ
  | [] => (33825, 0)
  | c :: w =>
    match wpairB a b U V w with
    | (P, F) => (mulB (if c then a else b) P,
        mulB (if c then a else b) F ^^^ mulB (if c then U else V) P)

theorem wpairB_spec (a b U V : ℕ) (w : List Bool) :
    bmat (wpairB a b U V w).1 = wprod (bmat a) (bmat b) w ∧
      bmat (wpairB a b U V w).2 = wfox (bmat a) (bmat b) (bmat U) (bmat V) w := by
  induction w with
  | nil => exact ⟨by simp [wpairB, bmat_one, wprod_nil], by simp [wpairB, bmat_zero, wfox]⟩
  | cons c w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases h : wpairB a b U V w with ⟨P, F⟩
    rw [h] at ih1 ih2
    simp only at ih1 ih2
    simp only [wpairB, h, wprod_cons, wfox]
    cases c <;> simp [bmat_mulB, bmat_xor, ih1, ih2]

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
