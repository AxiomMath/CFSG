module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

@[expose] def mrow : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, b :: bs => (if a % 2 = 1 then b else 0) ^^^ mrow (a / 2) bs

@[expose] def mmul (A B : List ℕ) : List ℕ := A.map fun a => mrow a B

@[expose] def mone : List ℕ := [1, 2, 4, 8, 16, 32]

@[expose] def mpow (A : List ℕ) : ℕ → List ℕ
  | 0 => mone
  | n + 1 => mmul A (mpow A n)

@[expose] def ind (R : Type*) [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

@[expose] def real (R : Type*) [Zero R] [One R] (A : List ℕ) : Matrix (Fin 6) (Fin 6) R :=
  Matrix.of fun i j => ind R ((A.getD i 0).testBit j)

section Ring

variable {R : Type*} [CommRing R] [CharP R 2]

theorem ind_xor (p q : Bool) : ind R (xor p q) = ind R p + ind R q := by
  cases p <;> cases q <;> simp [ind, CharTwo.add_self_eq_zero]

theorem ind_and (p q : Bool) : ind R (p && q) = ind R p * ind R q := by
  cases p <;> cases q <;> simp [ind]

theorem mrow_zero : ∀ B : List ℕ, mrow 0 B = 0
  | [] => rfl
  | _ :: bs => by
    rw [mrow]
    simp only [Nat.zero_mod, zero_ne_one, ↓reduceIte, Nat.zero_div, Nat.zero_xor]
    exact mrow_zero bs

theorem ind_testBit_mrow (a : ℕ) (B : List ℕ) (j : ℕ) :
    ind R ((mrow a B).testBit j) =
      ∑ k ∈ Finset.range B.length, ind R (a.testBit k) * ind R ((B.getD k 0).testBit j) := by
  induction B generalizing a with
  | nil => simp [mrow, ind]
  | cons b bs ih =>
    rw [mrow, Nat.testBit_xor, ind_xor, ih (a / 2), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.testBit_div_two]
    rw [add_comm]
    congr 1
    by_cases ha : a % 2 = 1
    · have h0 : a.testBit 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.1 ha
      simp [ha, h0, ind]
    · have h0 : a.testBit 0 = false := by
        rw [Nat.testBit_zero]
        simpa using ha
      simp [ha, h0, ind]

theorem getD_mmul (A B : List ℕ) (i : ℕ) : (mmul A B).getD i 0 = mrow (A.getD i 0) B := by
  rw [mmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  rcases A[i]? with _ | a
  · simp [mrow_zero]
  · simp

theorem real_mmul (A B : List ℕ) (hB : B.length = 6) :
    real R (mmul A B) = real R A * real R B := by
  ext i j
  simp only [real, Matrix.of_apply, Matrix.mul_apply]
  rw [getD_mmul, ind_testBit_mrow, hB, ← Fin.sum_univ_eq_sum_range]

theorem testBit_mone : ∀ i j : Fin 6, (mone.getD i 0).testBit j = decide (i = j) := by
  decide

theorem real_mone : real R mone = (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  simp only [real, Matrix.of_apply, testBit_mone, ind, Matrix.one_apply, decide_eq_true_eq]

theorem length_mmul (A B : List ℕ) : (mmul A B).length = A.length := by
  simp [mmul]

theorem length_mpow (A : List ℕ) (hA : A.length = 6) : ∀ n, (mpow A n).length = 6
  | 0 => rfl
  | n + 1 => by rw [mpow, length_mmul, hA]

theorem real_mpow (A : List ℕ) (hA : A.length = 6) :
    ∀ n, real R (mpow A n) = real R A ^ n
  | 0 => by rw [mpow, real_mone, pow_zero]
  | n + 1 => by rw [mpow, real_mmul _ _ (length_mpow A hA n), real_mpow A hA n, pow_succ']

end Ring

@[expose] def mkRow (f : Fin 6 → Bool) : ℕ :=
  (f 0).toNat + 2 * (f 1).toNat + 4 * (f 2).toNat + 8 * (f 3).toNat + 16 * (f 4).toNat +
    32 * (f 5).toNat

theorem testBit_mkRow : ∀ (f : Fin 6 → Bool) (j : Fin 6), (mkRow f).testBit j = f j := by
  decide

theorem mkRow_lt : ∀ f : Fin 6 → Bool, mkRow f < 64 := by
  decide

@[expose] def maskOf {R : Type*} [Zero R] [DecidableEq R] (M : Matrix (Fin 6) (Fin 6) R) :
    List ℕ :=
  (List.finRange 6).map fun i => mkRow fun j => decide (M i j ≠ 0)

theorem length_maskOf {R : Type*} [Zero R] [DecidableEq R] (M : Matrix (Fin 6) (Fin 6) R) :
    (maskOf M).length = 6 := by
  simp [maskOf]

theorem getD_maskOf {R : Type*} [Zero R] [DecidableEq R] (M : Matrix (Fin 6) (Fin 6) R)
    (i : Fin 6) : (maskOf M).getD i 0 = mkRow fun j => decide (M i j ≠ 0) := by
  rw [maskOf, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem real_maskOf {R : Type*} [Zero R] [One R] [DecidableEq R] (h01 : ∀ c : R, c = 0 ∨ c = 1)
    (M : Matrix (Fin 6) (Fin 6) R) : real R (maskOf M) = M := by
  ext i j
  simp only [real, Matrix.of_apply, getD_maskOf, testBit_mkRow, ind]
  rcases h01 (M i j) with h | h
  · simp [h]
  · by_cases h1 : (1 : R) = 0
    · rw [h, h1]
      simp
    · simp [h, h1]

theorem real_injective {R : Type*} [Zero R] [One R] [NeZero (1 : R)] {A B : List ℕ}
    (hA : A.length = 6) (hB : B.length = 6) (hA' : ∀ a ∈ A, a < 64) (hB' : ∀ b ∈ B, b < 64)
    (h : real R A = real R B) : A = B := by
  refine List.ext_getElem (hA.trans hB.symm) fun i hiA hiB => ?_
  have hi : i < 6 := hA ▸ hiA
  have hAi := hA' _ (List.getElem_mem hiA)
  have hBi := hB' _ (List.getElem_mem hiB)
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 6
  · have e := congrArg (fun M : Matrix (Fin 6) (Fin 6) R => M ⟨i, hi⟩ ⟨j, hj⟩) h
    simp only [real, Matrix.of_apply, ind, List.getD_eq_getElem _ _ hiA,
      List.getD_eq_getElem _ _ hiB] at e
    by_cases h1 : A[i].testBit j <;> by_cases h2 : B[i].testBit j <;> simp_all
  · have h64 : (64 : ℕ) ≤ 2 ^ j := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hAi h64),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hBi h64)]

theorem maskOf_lt {R : Type*} [Zero R] [DecidableEq R] (M : Matrix (Fin 6) (Fin 6) R) :
    ∀ a ∈ maskOf M, a < 64 := by
  intro a ha
  simp only [maskOf, List.mem_map] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact mkRow_lt _

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
