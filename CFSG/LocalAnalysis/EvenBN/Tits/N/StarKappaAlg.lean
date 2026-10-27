module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Star

open Matrix

@[expose] def kapA : Matrix (Fin 5) (Fin 5) (ZMod 4) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 1, 1, 0, 1, 0; 1, 1, 1, 0, 1]

@[expose] def kapA2 : Matrix (Fin 5) (Fin 5) (ZMod 4) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 2, 0, 1, 0, 0; 2, 2, 0, 1, 0; 3, 2, 2, 0, 1]

theorem kapA_mul_self : kapA * kapA = kapA2 := by
  decide

theorem kapA2_mul_self_apply :
    (kapA2 * kapA2) 4 0 = 2 ∧ (kapA2 * kapA2) 4 1 = 0 ∧ (kapA2 * kapA2) 4 2 = 0 := by
  decide

theorem kapA2_apply : kapA2 1 2 = 0 ∧ kapA2 2 2 = 1 := by
  decide

theorem kapA2_mul_apply_four (W : Matrix (Fin 5) (Fin 5) (ZMod 4)) (j : Fin 5) :
    (kapA2 * W) 4 j = 3 * W 0 j + 2 * W 1 j + 2 * W 2 j + W 4 j := by
  simp [kapA2, Matrix.mul_apply, Fin.sum_univ_five]

theorem mul_kapA2_apply_zero (W : Matrix (Fin 5) (Fin 5) (ZMod 4)) (i : Fin 5) :
    (W * kapA2) i 0 = W i 0 + 2 * W i 2 + 2 * W i 3 + 3 * W i 4 := by
  simp [kapA2, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul_kapA2_apply_one (W : Matrix (Fin 5) (Fin 5) (ZMod 4)) (i : Fin 5) :
    (W * kapA2) i 1 = W i 1 + 2 * W i 3 + 2 * W i 4 := by
  simp [kapA2, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem mul_kapA2_apply_two (W : Matrix (Fin 5) (Fin 5) (ZMod 4)) (i : Fin 5) :
    (W * kapA2) i 2 = W i 2 + 2 * W i 4 := by
  simp [kapA2, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem two_mul_trace_eq_zero (Y : Matrix (Fin 5) (Fin 5) (ZMod 4)) :
    2 * ((kapA * Y + Y * kapA) 0 0 + (kapA * Y + Y * kapA) 0 1 + (kapA * Y + Y * kapA) 0 2 +
      (kapA * Y + Y * kapA) 1 2 + (kapA * Y + Y * kapA) 2 2 + (kapA * Y + Y * kapA) 4 4) = 0 := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_five]
  simp [kapA]
  linear_combination (Y 0 0 + Y 0 1 + 2 * Y 0 2 + Y 0 3 + 2 * Y 0 4 + Y 1 2 + Y 1 4 + Y 2 2 +
      Y 2 4 + Y 4 4) * h4

theorem mul_self_add_two_nsmul (X W : Matrix (Fin 5) (Fin 5) (ZMod 4)) :
    (X + 2 • W) * (X + 2 • W) = X * X + 2 • (X * W + W * X) := by
  have h4 : (2 • W) * (2 • W) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul]
    have h : ((2 * 2 : ℕ) : ZMod 4) = 0 := by decide
    rw [h, zero_mul]
  rw [add_mul, mul_add, mul_add, h4, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    add_assoc]

theorem exists_eq_add_two_mul_of_two_mul_eq :
    ∀ b a : ZMod 4, 2 * b = 2 * a → ∃ y : ZMod 4, b = a + 2 * y := by
  decide

theorem false_of_kapMatrix (B : Matrix (Fin 5) (Fin 5) (ZMod 4))
    (h2 : ∀ i j, 2 * B i j = 2 * kapA i j) (hQQ : B * B * (B * B) = 1)
    (h12 : (B * B) 1 2 = 0) (h22 : (B * B) 2 2 = 1) : False := by
  choose Y hY using fun i j => exists_eq_add_two_mul_of_two_mul_eq (B i j) (kapA i j) (h2 i j)
  set Ym : Matrix (Fin 5) (Fin 5) (ZMod 4) := Matrix.of Y with hYm
  set W : Matrix (Fin 5) (Fin 5) (ZMod 4) := kapA * Ym + Ym * kapA with hW
  have hB : B = kapA + 2 • Ym := by
    ext i j
    rw [hY i j, Matrix.add_apply, Matrix.smul_apply, hYm, Matrix.of_apply, nsmul_eq_mul]
    norm_num
  have hQ : B * B = kapA2 + 2 • W := by
    rw [hB, mul_self_add_two_nsmul, kapA_mul_self]
  have hQ2 : B * B * (B * B) = kapA2 * kapA2 + 2 • (kapA2 * W + W * kapA2) := by
    rw [hQ, mul_self_add_two_nsmul]
  obtain ⟨a40, a41, a42⟩ := kapA2_mul_self_apply
  obtain ⟨a12, a22⟩ := kapA2_apply
  have h4 : (4 : ZMod 4) = 0 := by decide
  have e1 := congrFun (congrFun hQQ 4) 0
  have e2 := congrFun (congrFun hQQ 4) 1
  have e3 := congrFun (congrFun hQQ 4) 2
  rw [hQ2, Matrix.add_apply, a40, Matrix.smul_apply, Matrix.add_apply, kapA2_mul_apply_four,
    mul_kapA2_apply_zero, nsmul_eq_mul, Matrix.one_apply_ne (by decide)] at e1
  rw [hQ2, Matrix.add_apply, a41, Matrix.smul_apply, Matrix.add_apply, kapA2_mul_apply_four,
    mul_kapA2_apply_one, nsmul_eq_mul, Matrix.one_apply_ne (by decide)] at e2
  rw [hQ2, Matrix.add_apply, a42, Matrix.smul_apply, Matrix.add_apply, kapA2_mul_apply_four,
    mul_kapA2_apply_two, nsmul_eq_mul, Matrix.one_apply_ne (by decide)] at e3
  rw [hQ, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, a12] at h12
  rw [hQ, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, a22] at h22
  push_cast at e1 e2 e3 h12 h22
  have c1 : 2 + 2 * W 0 0 + 2 * W 4 4 = 0 := by
    linear_combination e1 - (W 0 0 + W 1 0 + W 2 0 + W 4 0 + W 4 2 + W 4 3 + W 4 4) * h4
  have c2 : 2 * W 0 1 = 0 := by
    linear_combination e2 - (W 0 1 + W 1 1 + W 2 1 + W 4 1 + W 4 3 + W 4 4) * h4
  have c3 : 2 * W 0 2 = 0 := by
    linear_combination e3 - (W 0 2 + W 1 2 + W 2 2 + W 4 2 + W 4 4) * h4
  have c6 := two_mul_trace_eq_zero Ym
  have : (2 : ZMod 4) = 0 := by linear_combination c1 - c6 + c2 + c3 + h12 + h22
  exact absurd this (by decide)

end CFSG.LocalAnalysis.EvenBN.Tits.N.Star
