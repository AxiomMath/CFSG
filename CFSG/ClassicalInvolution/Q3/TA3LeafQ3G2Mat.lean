module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.SL3

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

variable (F) in
@[expose] def i₀ : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

@[expose] def j₀ (h3 : (3 : F) = 0) : SL(2, F) :=
  ⟨!![1, 1; 1, -1], by rw [det_fin_two_of]; linear_combination -h3⟩

variable (F) in
@[expose] def x₀ : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

theorem i₀_sq : i₀ F ^ 2 = -1 := by
  rw [pow_two]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [i₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem j₀_sq (h3 : (3 : F) = 0) : j₀ h3 ^ 2 = -1 := by
  rw [pow_two]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [j₀, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h3

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
  exact h2 (by simpa [neg_eq_iff_add_eq_zero, one_add_one_eq_two] using this)

theorem pow_four_of_sq {g : SL(2, F)} (h : g ^ 2 = -1) : g ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, h, neg_one_sq]

theorem x₀_pow_three (h3 : (3 : F) = 0) : x₀ F ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [x₀, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h3

theorem x₀_ne_one : x₀ F ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [x₀] at this

theorem eq_smul_one_of_commute (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 2) (Fin 2) F)
    (hi : M * !![0, 1; -1, 0] = !![0, 1; -1, 0] * M)
    (hj : M * !![1, 1; 1, -1] = !![1, 1; 1, -1] * M) : M = M 0 0 • 1 := by
  have e1 := congrFun (congrFun hi 0) 0
  have e2 := congrFun (congrFun hi 0) 1
  have e3 := congrFun (congrFun hj 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hq : M 0 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination e3 - e1 : 2 * M 0 1 = 0)).resolve_left h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact hq
  · linear_combination -e1 - hq
  · linear_combination -e2

theorem eq_one_or_eq_neg_one_of_commute (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0) {g : SL(2, F)}
    (hi : g * i₀ F = i₀ F * g) (hj : g * j₀ h3 = j₀ h3 * g) : g = 1 ∨ g = -1 := by
  have hM := eq_smul_one_of_commute h2 (g : Matrix (Fin 2) (Fin 2) F)
    (congrArg Subtype.val hi) (congrArg Subtype.val hj)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := g.2
    rw [hM, Matrix.det_smul, Matrix.det_one] at this
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp hdet with h | h
  · left
    ext i j
    rw [hM, h]
    simp
  · right
    ext i j
    rw [hM, h]
    simp

theorem isSquare_det_of_commute (h2 : (2 : F) ≠ 0) (P : GL (Fin 2) F)
    (hi : (P : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] =
      !![0, 1; -1, 0] * (P : Matrix (Fin 2) (Fin 2) F))
    (hj : (P : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 1, -1] =
      !![1, 1; 1, -1] * (P : Matrix (Fin 2) (Fin 2) F)) :
    IsSquare ((Matrix.GeneralLinearGroup.det P : Fˣ) : F) := by
  refine ⟨(P : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, eq_smul_one_of_commute h2 _ hi hj,
    Matrix.det_smul, Matrix.det_one]
  simp [sq]

end CFSG.ClassicalInvolution.Q3.TA3.SL3
