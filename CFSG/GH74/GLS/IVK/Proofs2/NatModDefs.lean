module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.EuclideanDomain.Field

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix

variable {F : Type*} [Field F]

@[expose] def upperSL (c : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

@[expose] def lowerSL (c : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; c, 1], by simp [det_fin_two]⟩

@[expose] def diagSL (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [det_fin_two]⟩

@[expose] def weylSL (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, (a : F); -((a⁻¹ : Fˣ) : F), 0], by simp [det_fin_two]⟩

theorem coe_upperSL (c : F) : ((upperSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, c; 0, 1] := rfl

theorem coe_lowerSL (c : F) : ((lowerSL c : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 0; c, 1] := rfl

theorem coe_diagSL (a : Fˣ) : ((diagSL a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] := rfl

theorem coe_weylSL (a : Fˣ) : ((weylSL a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![0, (a : F); -((a⁻¹ : Fˣ) : F), 0] := rfl

theorem upperSL_add (c d : F) : upperSL c * upperSL d = upperSL (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_upperSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperSL_zero : (upperSL 0 : SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_upperSL]

theorem lowerSL_add (c d : F) : lowerSL c * lowerSL d = lowerSL (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerSL_zero : (lowerSL 0 : SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_lowerSL]

theorem diagSL_mul (a b : Fˣ) : (diagSL a * diagSL b : SpecialLinearGroup (Fin 2) F) = diagSL (a * b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem weylSL_eq (a : Fˣ) :
    (weylSL a : SpecialLinearGroup (Fin 2) F) =
      upperSL (a : F) * lowerSL (-((a⁻¹ : Fˣ) : F)) * upperSL (a : F) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_upperSL, coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_mul_lowerSL (a : Fˣ) (c : F) :
    (weylSL a : SpecialLinearGroup (Fin 2) F) * lowerSL c = upperSL (-((a : F) ^ 2 * c)) * weylSL a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_upperSL, coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem diagSL_eq_weylSL (a : Fˣ) :
    (diagSL a : SpecialLinearGroup (Fin 2) F) = weylSL a * (weylSL 1)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL, coe_weylSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem weylSL_one_mul_self :
    (weylSL 1 : SpecialLinearGroup (Fin 2) F) * weylSL 1 = diagSL (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL, coe_weylSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagSL_mul_lowerSL (a : Fˣ) (c : F) :
    (diagSL a : SpecialLinearGroup (Fin 2) F) * lowerSL c =
      lowerSL (((a⁻¹ : Fˣ) : F) ^ 2 * c) * diagSL a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_lowerSL, Matrix.mul_apply, Fin.sum_univ_two]
  have ha : (a : F) ≠ 0 := a.ne_zero
  field_simp

end CFSG.GH74.GLS.IVK.Proofs2
