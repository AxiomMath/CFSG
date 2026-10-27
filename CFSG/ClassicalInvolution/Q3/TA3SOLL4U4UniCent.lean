module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniFrame

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_one_of_mul_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    {M M' N : Matrix n n K} (hM : M * M' = 1) (hM' : M' * M = 1) {c : K}
    (hc : M * N = c • (N * M)) (hN : N.trace ≠ 0) : c = 1 := by
  have h1 : M * N * M' = c • N := by
    rw [hc, Matrix.smul_mul, Matrix.mul_assoc, hM, Matrix.mul_one]
  have h2 : (M * N * M').trace = N.trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hM', Matrix.mul_one]
  rw [h1, trace_smul, smul_eq_mul] at h2
  exact (mul_eq_right₀ hN).mp h2

theorem trace_fromBlocks_unip {A D : Matrix (Fin 2) (Fin 2) K} (hA : A.trace = 2)
    (hD : D.trace = 2) : (fromBlocks A 0 0 D).trace = 4 := by
  have : (fromBlocks A 0 0 D).trace = A.trace + D.trace := by
    simp only [Matrix.trace, Fintype.sum_sum_type, diag_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₂₂]
  rw [this, hA, hD]; norm_num

theorem trace_upper (t : K) : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).trace = 2 := by
  rw [trace_fin_two_of]; norm_num

theorem trace_lower (s : K) : (!![1, 0; s, 1] : Matrix (Fin 2) (Fin 2) K).trace = 2 := by
  rw [trace_fin_two_of]; norm_num

theorem leviStar_upper (t : K) :
    leviStar h !![1, t; 0, 1] = !![1, 0; -h.bar t, 1] := by
  rw [leviStar, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem leviStar_lower (s : K) :
    leviStar h !![1, 0; s, 1] = !![1, -h.bar s; 0, 1] := by
  rw [leviStar, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_smul_one_of_comm_unip {P : Matrix (Fin 2) (Fin 2) K} {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : P * !![1, d; 0, 1] = !![1, d; 0, 1] * P) (h2 : P * !![1, 0; c, 1] = !![1, 0; c, 1] * P) :
    P = P 0 0 • 1 := by
  have x1 := congrFun (congrFun h1 0) 0
  have x2 := congrFun (congrFun h1 0) 1
  have x3 := congrFun (congrFun h2 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, one_mul, mul_zero, zero_mul, add_zero] at x1 x2 x3
  have y1 : P 1 0 = 0 :=
    (mul_eq_zero.mp (by linear_combination (-1 : K) * x1 : d * P 1 0 = 0)).resolve_left hd
  have y2 : P 1 1 = P 0 0 := by
    have := (mul_eq_zero.mp (by linear_combination (-1 : K) * x2 :
      d * (P 1 1 - P 0 0) = 0)).resolve_left hd
    linear_combination this
  have y3 : P 0 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination x3 : P 0 1 * c = 0)).resolve_right hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y1, y2, y3]

theorem eq_zero_of_twist_left {Q : Matrix (Fin 2) (Fin 2) K} {τ : K} (h2 : (2 : K) ≠ 0)
    (hτ : τ ≠ 0) (h1 : Q * !![1, 0; -1, 1] = !![1, 1; 0, 1] * Q)
    (h3 : Q * !![1, 0; τ, 1] = !![1, τ; 0, 1] * Q)
    (h4 : Q * !![1, -1; 0, 1] = !![1, 0; 1, 1] * Q) : Q = 0 := by
  have x1 := congrFun (congrFun h1 0) 0
  have x2 := congrFun (congrFun h1 0) 1
  have x3 := congrFun (congrFun h3 0) 0
  have x4 := congrFun (congrFun h4 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, mul_neg] at x1 x2 x3 x4
  have y11 : Q 1 1 = 0 := by linear_combination (-1 : K) * x2
  have y00 : Q 0 0 = 0 := by linear_combination (-1 : K) * x4
  have b : Q 0 1 = Q 1 0 := by
    have := (mul_eq_zero.mp (by linear_combination x3 : τ * (Q 0 1 - Q 1 0) = 0)).resolve_left hτ
    linear_combination this
  have y10 : Q 1 0 = 0 :=
    (mul_eq_zero.mp (by linear_combination (-1 : K) * x1 - b : 2 * Q 1 0 = 0)).resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y00, y11, y10, b]

theorem eq_zero_of_twist_right {R : Matrix (Fin 2) (Fin 2) K} {τ : K} (h2 : (2 : K) ≠ 0)
    (hτ : τ ≠ 0) (h1 : R * !![1, 1; 0, 1] = !![1, 0; -1, 1] * R)
    (h3 : R * !![1, τ; 0, 1] = !![1, 0; τ, 1] * R)
    (h4 : R * !![1, 0; 1, 1] = !![1, -1; 0, 1] * R) : R = 0 := by
  have x1 := congrFun (congrFun h1 0) 1
  have x2 := congrFun (congrFun h1 1) 1
  have x3 := congrFun (congrFun h3 1) 1
  have x4 := congrFun (congrFun h4 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, one_mul, zero_mul, add_zero, zero_add, neg_mul] at x1 x2 x3 x4
  have y00 : R 0 0 = 0 := by linear_combination x1
  have y11 : R 1 1 = 0 := by linear_combination x4
  have b : R 1 0 = R 0 1 := by
    have := (mul_eq_zero.mp (by linear_combination x3 : τ * (R 1 0 - R 0 1) = 0)).resolve_left hτ
    linear_combination this
  have y01 : R 0 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination x2 - b : 2 * R 0 1 = 0)).resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y00, y11, y01, b]

theorem eq_fromBlocks_smul_of_comm {τ : K} (h2 : (2 : K) ≠ 0) (hτ : τ ≠ 0)
    (hτb : h.bar τ = -τ) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hu1 : M * fromBlocks !![1, 1; 0, 1] 0 0 !![1, 0; -h.bar 1, 1] =
      fromBlocks !![1, 1; 0, 1] 0 0 !![1, 0; -h.bar 1, 1] * M)
    (huτ : M * fromBlocks !![1, τ; 0, 1] 0 0 !![1, 0; -h.bar τ, 1] =
      fromBlocks !![1, τ; 0, 1] 0 0 !![1, 0; -h.bar τ, 1] * M)
    (hl : M * fromBlocks !![1, 0; 1, 1] 0 0 !![1, -h.bar 1; 0, 1] =
      fromBlocks !![1, 0; 1, 1] 0 0 !![1, -h.bar 1; 0, 1] * M) :
    ∃ a b : K, M = fromBlocks (a • 1) 0 0 (b • 1) := by
  rw [map_one] at hu1 hl
  rw [hτb, neg_neg] at huτ
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply] at hu1 huτ hl
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hu1 huτ hl
  obtain ⟨a1, b1, c1, d1⟩ := fromBlocks_inj.mp hu1
  obtain ⟨-, b2, c2, -⟩ := fromBlocks_inj.mp huτ
  obtain ⟨a3, b3, c3, d3⟩ := fromBlocks_inj.mp hl
  refine ⟨M.toBlocks₁₁ 0 0, M.toBlocks₂₂ 0 0, ?_⟩
  rw [← fromBlocks_toBlocks M]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
  rw [← eq_smul_one_of_comm_unip one_ne_zero one_ne_zero a1 a3,
    ← eq_smul_one_of_comm_unip (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero) d3 d1,
    eq_zero_of_twist_left h2 hτ b1 b2 b3, eq_zero_of_twist_right h2 hτ c1 c2 c3]

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
