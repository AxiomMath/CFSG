module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def fhLevT : SL(4, F) :=
  ⟨!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

@[expose] def fhLevL : SL(4, F) :=
  ⟨!![1, 0, 0, 0; -1, 1, 0, 0; 0, 0, 1, 0; 0, 0, -1, 1],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

@[expose] def fhLevY : SL(4, F) :=
  ⟨!![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem fhLevT_pow_three (h3 : (3 : F) = 0) : (fhLevT : SL(4, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevT, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h3 | linear_combination (-1 : F) * h3

theorem fhLevL_pow_three (h3 : (3 : F) = 0) : (fhLevL : SL(4, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevL, pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h3 | linear_combination (-1 : F) * h3

theorem fhLevW_val : ((fhLevT * fhLevL * fhLevT : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fhLevT, fhLevL, Matrix.mul_apply, Fin.sum_univ_four]

theorem fhLevW_sq : ((fhLevT * fhLevL * fhLevT : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
    ((fhLevT * fhLevL * fhLevT : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := by
  rw [fhLevW_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem fhLevY_sq : ((fhLevY : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
    ((fhLevY : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fhLevY, Matrix.mul_apply, Fin.sum_univ_four]

theorem fhLevT_comm_Y : (fhLevT : SL(4, F)) * fhLevY = fhLevY * fhLevT := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevT, fhLevY, Matrix.mul_apply, Fin.sum_univ_four]

theorem fhLevL_comm_Y : (fhLevL : SL(4, F)) * fhLevY = fhLevY * fhLevL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevL, fhLevY, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def fhLevU2 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def fhLevL2 : SL(2, F) := ⟨!![1, 0; -1, 1], by simp [Matrix.det_fin_two]⟩

theorem fhLevU2_pow_three (h3 : (3 : F) = 0) : (fhLevU2 : SL(2, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevU2, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h3 | linear_combination (-1 : F) * h3

theorem fhLevL2_pow_three (h3 : (3 : F) = 0) : (fhLevL2 : SL(2, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fhLevL2, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h3 | linear_combination (-1 : F) * h3

theorem fhLevJ2_val : ((fhLevU2 * fhLevL2 * fhLevU2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fhLevU2, fhLevL2, Matrix.mul_apply, Fin.sum_univ_two]

theorem fhLevJ2_sq : ((fhLevU2 * fhLevL2 * fhLevU2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
    ((fhLevU2 * fhLevL2 * fhLevU2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [fhLevJ2_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end CFSG.OddStandard.SmallF3.Omega
