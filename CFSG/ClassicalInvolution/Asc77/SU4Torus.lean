module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def torusW (u : Fˣ) : SL(2, F) :=
  ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

theorem coe_torusW (u : Fˣ) :
    ((torusW u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(u : F), ((u⁻¹ : Fˣ) : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torusW]

theorem coe_torusW_inv (u : Fˣ) :
    (((torusW u)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![((u⁻¹ : Fˣ) : F), (u : F)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_torusW]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem units_sq_eq_neg_one {u : Fˣ} (hu : u ^ 2 = -1) : (u : F) * (u : F) = -1 := by
  have := congrArg (fun v : Fˣ => (v : F)) hu
  simpa [sq] using this

theorem units_inv_eq_neg {u : Fˣ} (hu : u ^ 2 = -1) : ((u⁻¹ : Fˣ) : F) = -(u : F) := by
  have : (u : F) * (-(u : F)) = 1 := by linear_combination -units_sq_eq_neg_one hu
  rw [Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right this

theorem torusW_mul_self {u : Fˣ} (hu : u ^ 2 = -1) : torusW u * torusW u = (-1 : SL(2, F)) := by
  have hu0 := units_sq_eq_neg_one hu
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_torusW, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [units_inv_eq_neg hu, hu0]

theorem diagConj2_sq {u : Fˣ} (hu : u ^ 2 = -1) (s : SL(2, F)) :
    diagConj2 u⁻¹ 1 (diagConj2 u⁻¹ 1 s) = torusW u * s * (torusW u)⁻¹ := by
  have hu0 := units_sq_eq_neg_one hu
  have hu1 := units_inv_eq_neg hu
  ext i j
  simp only [coe_diagConj2, Matrix.SpecialLinearGroup.coe_mul, coe_torusW, coe_torusW_inv,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Units.val_one, inv_one, inv_inv, hu1]
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination ((s : Matrix (Fin 2) (Fin 2) F) 0 0 * (u : F) * (u : F)) * hu0
  · ring
  · ring
  · linear_combination ((s : Matrix (Fin 2) (Fin 2) F) 1 1) * hu0

theorem coe_blockSL_torusW (u : Fˣ) :
    ((blockSL F 3 2 0 (by omega) (torusW u) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(u : F), ((u⁻¹ : Fˣ) : F), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_blockSL_three_zero, coe_torusW]

theorem coe_blockSL_torusW_inv (u : Fˣ) :
    (((blockSL F 3 2 0 (by omega) (torusW u))⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![((u⁻¹ : Fˣ) : F), (u : F), 1] := by
  rw [← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_blockSL_three_zero, coe_torusW]

theorem blockSL_torusW_conj (u : Fˣ) (s : SL(2, F)) :
    blockSL F 3 2 0 (by omega) (torusW u) * blockSL F 3 2 1 (by omega) s *
        (blockSL F 3 2 0 (by omega) (torusW u))⁻¹ =
      blockSL F 3 2 1 (by omega) (diagConj2 u⁻¹ 1 s) := by
  have h1 : blockSL F 3 2 0 (by omega) (torusW u) * blockSL F 3 2 1 (by omega) s *
      (blockSL F 3 2 0 (by omega) (torusW u))⁻¹ =
        diagConj3 u u⁻¹ (blockSL F 3 2 1 (by omega) s) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagConj3, coe_blockSL_torusW,
      coe_blockSL_torusW_inv, Matrix.diagonal_mul, Matrix.mul_diagonal, Units.val_inv_eq_inv_val,
      inv_inv]
  rw [h1, diagConj3_blockSL_one]

theorem torusW_inv (u : Fˣ) : (torusW u)⁻¹ = torusW (F := F) u⁻¹ := by
  ext i j
  rw [coe_torusW_inv, coe_torusW]
  simp

theorem blockSL_torusW_inv_conj (u : Fˣ) (s : SL(2, F)) :
    (blockSL F 3 2 0 (by omega) (torusW u))⁻¹ * blockSL F 3 2 1 (by omega) s *
        blockSL F 3 2 0 (by omega) (torusW u) =
      blockSL F 3 2 1 (by omega) (diagConj2 u 1 s) := by
  have h := blockSL_torusW_conj (F := F) u⁻¹ s
  rw [← torusW_inv, map_inv, inv_inv, inv_inv] at h
  exact h

theorem exists_unit_sq_eq_neg_one [Finite F] (h : Nat.card F % 4 = 1) : ∃ u : Fˣ, u ^ 2 = -1 := by
  have := Fintype.ofFinite F
  have hsq : IsSquare (-1 : F) :=
    FiniteField.isSquare_neg_one_iff.mpr (by rw [← Nat.card_eq_fintype_card]; omega)
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [sq, hr])⟩

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
