module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix

variable {K : Type} [Field K]

theorem det_sq_eq_one_of_isometry {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → K}
    (hw : ∀ i, w i ≠ 0) {Y : Matrix ι ι K} (hY : Yᵀ * diagonal w * Y = diagonal w) :
    Y.det ^ 2 = 1 := by
  have e := congrArg Matrix.det hY
  rw [det_mul, det_mul, det_transpose, det_diagonal] at e
  have h0 : ∏ i, w i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hw i
  have h : (Y.det ^ 2 - 1) * ∏ i, w i = 0 := by linear_combination e
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right h0)

theorem binary_gram_apply (w : Fin 2 → K) (Y : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (Yᵀ * diagonal w * Y) i j = Y 0 i * w 0 * Y 0 j + Y 1 i * w 1 * Y 1 j := by
  rw [mul_apply, Fin.sum_univ_two, mul_diagonal, mul_diagonal, transpose_apply, transpose_apply]

theorem binary_mul_apply (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [mul_apply, Fin.sum_univ_two]

omit [Field K] in
theorem binary_ext {A B : Matrix (Fin 2) (Fin 2) K} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  rw [eta_fin_two A, eta_fin_two B, h00, h01, h10, h11]

theorem binary_isometry_entries {w : Fin 2 → K} (hw : ∀ i, w i ≠ 0)
    {Y : Matrix (Fin 2) (Fin 2) K} (hY : Yᵀ * diagonal w * Y = diagonal w) :
    Y 1 1 = Y.det * Y 0 0 ∧ Y.det * Y 1 0 * w 1 = -(w 0 * Y 0 1) := by
  have h00 := congrFun (congrFun hY 0) 0
  have h01 := congrFun (congrFun hY 0) 1
  rw [binary_gram_apply, diagonal_apply_eq] at h00
  rw [binary_gram_apply, diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)] at h01
  rw [det_fin_two]
  refine ⟨?_, by linear_combination (-Y 0 1) * h00 + Y 0 0 * h01⟩
  have h : w 0 * (Y 1 1 - (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) * Y 0 0) = 0 := by
    linear_combination (-Y 1 1) * h00 + Y 1 0 * h01
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (hw 0))

variable {n : ℕ} {w : Fin n → K}

theorem mul_self_eq_one_of_det_eq_neg_one (hn : n = 2) (hw : ∀ i, w i ≠ 0)
    {Y : Matrix (Fin n) (Fin n) K} (hY : Yᵀ * diagonal w * Y = diagonal w) (hd : Y.det = -1) :
    Y * Y = 1 := by
  subst hn
  obtain ⟨he, -⟩ := binary_isometry_entries hw hY
  rw [hd] at he
  rw [det_fin_two] at hd
  refine binary_ext ?_ ?_ ?_ ?_ <;> simp only [binary_mul_apply, one_apply_eq,
    one_apply_ne (by decide : (0 : Fin 2) ≠ 1), one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  · linear_combination (-1 : K) * hd + Y 0 0 * he
  · linear_combination Y 0 1 * he
  · linear_combination Y 1 0 * he
  · linear_combination (-1 : K) * hd + Y 1 1 * he

theorem commute_of_det_eq_one (hn : n = 2) (hw : ∀ i, w i ≠ 0)
    {Y Y' : Matrix (Fin n) (Fin n) K} (hY : Yᵀ * diagonal w * Y = diagonal w)
    (hY' : Y'ᵀ * diagonal w * Y' = diagonal w) (hd : Y.det = 1) (hd' : Y'.det = 1) :
    Y * Y' = Y' * Y := by
  subst hn
  obtain ⟨he, hc⟩ := binary_isometry_entries hw hY
  obtain ⟨he', hc'⟩ := binary_isometry_entries hw hY'
  rw [hd, one_mul] at he hc
  rw [hd', one_mul] at he' hc'
  have key : Y 0 1 * Y' 1 0 = Y' 0 1 * Y 1 0 := by
    have h : w 1 * (Y 0 1 * Y' 1 0 - Y' 0 1 * Y 1 0) = 0 := by
      linear_combination Y 0 1 * hc' - Y' 0 1 * hc
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (hw 1))
  refine binary_ext ?_ ?_ ?_ ?_ <;> simp only [binary_mul_apply]
  · linear_combination key
  · linear_combination Y 0 1 * he' - Y' 0 1 * he
  · linear_combination Y' 1 0 * he - Y 1 0 * he'
  · linear_combination (-1 : K) * key

theorem eq_one_or_eq_neg_one_of_det_eq_one (hn : n = 2) (h2 : (2 : K) ≠ 0)
    {Y : Matrix (Fin n) (Fin n) K} (hd : Y.det = 1) (hY2 : Y * Y = 1) : Y = 1 ∨ Y = -1 := by
  subst hn
  rw [det_fin_two] at hd
  have h00 := congrFun (congrFun hY2 0) 0
  have h01 := congrFun (congrFun hY2 0) 1
  have h10 := congrFun (congrFun hY2 1) 0
  have h11 := congrFun (congrFun hY2 1) 1
  simp only [binary_mul_apply, one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h00 h01 h10 h11
  have hs : Y 0 0 * (Y 0 0 + Y 1 1) = 2 := by linear_combination h00 + hd
  have hs0 : Y 0 0 + Y 1 1 ≠ 0 := fun h => h2 (by rw [← hs, h, mul_zero])
  have hb : Y 0 1 = 0 := by
    have h : Y 0 1 * (Y 0 0 + Y 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 h).resolve_right hs0
  have hc : Y 1 0 = 0 := by
    have h : Y 1 0 * (Y 0 0 + Y 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 h).resolve_right hs0
  have ha : Y 0 0 * Y 0 0 = 1 := by linear_combination h00 - Y 1 0 * hb
  have he : Y 1 1 = Y 0 0 := by
    have h : Y 0 0 * (Y 1 1 - Y 0 0) = 0 := by linear_combination hd - ha + Y 1 0 * hb
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (left_ne_zero_of_mul_eq_one ha))
  rcases mul_self_eq_one_iff.1 ha with h | h
  · left
    refine binary_ext ?_ ?_ ?_ ?_ <;> simp [h, hb, hc, he]
  · right
    refine binary_ext ?_ ?_ ?_ ?_ <;> simp [h, hb, hc, he]

theorem eq_or_eq_neg_of_commute (hn : n = 2) (h2 : (2 : K) ≠ 0) (hw : ∀ i, w i ≠ 0)
    {Y Y' : Matrix (Fin n) (Fin n) K} (hY : Yᵀ * diagonal w * Y = diagonal w)
    (hY' : Y'ᵀ * diagonal w * Y' = diagonal w) (hd : Y.det = -1) (hd' : Y'.det = -1)
    (hc : Y * Y' = Y' * Y) : Y' = Y ∨ Y' = -Y := by
  have hY2 := mul_self_eq_one_of_det_eq_neg_one hn hw hY hd
  have hY'2 := mul_self_eq_one_of_det_eq_neg_one hn hw hY' hd'
  clear hY'
  have hdet : (Y * Y').det = 1 := by rw [det_mul, hd, hd']; ring
  have hsq : Y * Y' * (Y * Y') = 1 := by
    calc Y * Y' * (Y * Y') = Y * (Y' * Y) * Y' := by simp only [Matrix.mul_assoc]
      _ = Y * Y * (Y' * Y') := by rw [← hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY2, hY'2, Matrix.one_mul]
  have hYY : Y' = Y * (Y * Y') := by rw [← Matrix.mul_assoc, hY2, Matrix.one_mul]
  rcases eq_one_or_eq_neg_one_of_det_eq_one hn h2 hdet hsq with h | h
  · left
    rw [hYY, h, Matrix.mul_one]
  · right
    rw [hYY, h, Matrix.mul_neg, Matrix.mul_one]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
