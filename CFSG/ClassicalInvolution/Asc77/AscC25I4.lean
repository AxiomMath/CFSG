module

public import CFSG.ClassicalInvolution.Asc77.AscC25V34
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I.Sp5

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def rotM : Matrix (Fin 2) (Fin 2) F := (2 : F)⁻¹ • !![1, -1; 1, 1]

theorem rotM_transpose_mul (h2 : (2 : F) ≠ 0) :
    (rotM : Matrix (Fin 2) (Fin 2) F)ᵀ * rotM = (2 : F)⁻¹ • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotM, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

@[expose] noncomputable def yMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks rotM rotM (-rotM) rotM

@[expose] noncomputable def uV : Fin 2 ⊕ Fin 2 → F := fun a =>
  match a with
  | Sum.inl i => if i = 0 then 1 else 0
  | Sum.inr i => if i = 1 then 1 else 0

@[expose] noncomputable def wV : Fin 2 ⊕ Fin 2 → F := fun a =>
  match a with
  | Sum.inl i => if i = 1 then -(2 : F)⁻¹ else 0
  | Sum.inr i => if i = 0 then (2 : F)⁻¹ else 0

theorem form_uV_wV (h2 : (2 : F) ≠ 0) : form (uV : Fin 2 ⊕ Fin 2 → F) wV = 1 := by
  simp [form, dotProduct, Matrix.mulVec, gram, uV, wV, Fintype.sum_sum_type, Matrix.fromBlocks]
  rw [← two_mul, mul_inv_cancel₀ h2]

theorem form_v_uV (v : Fin 2 ⊕ Fin 2 → F) :
    form v uV = v (Sum.inl 1) - v (Sum.inr 0) := by
  simp [form, dotProduct, Matrix.mulVec, gram, uV, Fintype.sum_sum_type, Matrix.fromBlocks,
    Fin.sum_univ_two]
  ring

theorem form_v_wV (v : Fin 2 ⊕ Fin 2 → F) :
    form v wV = (2 : F)⁻¹ * (v (Sum.inl 0) + v (Sum.inr 1)) := by
  simp [form, dotProduct, Matrix.mulVec, gram, wV, Fintype.sum_sum_type, Matrix.fromBlocks,
    Fin.sum_univ_two]
  ring

theorem yMat_symp (h2 : (2 : F) ≠ 0) :
    (yMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * gram F 2 * yMat = gram F 2 := by
  have h := rotM_transpose_mul (F := F) h2
  rw [yMat, gram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_neg, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [h]
  have h22 : ((2 : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)) + (2 : F)⁻¹ • 1 = 1 := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have e1 : -(-((2 : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F))) + -((2 : F)⁻¹ • 1) = 0 := by
    rw [neg_neg, add_neg_cancel]
  have e2 : -(-((2 : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F))) + (2 : F)⁻¹ • 1 = 1 := by
    rw [neg_neg, h22]
  have e3 : -((2 : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)) + -((2 : F)⁻¹ • 1) = -1 := by
    rw [← neg_add, h22]
  have e4 : -((2 : F)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)) + (2 : F)⁻¹ • 1 = 0 := by
    rw [neg_add_cancel]
  rw [e1, e2, e3, e4]

@[expose] noncomputable def yEl (h2 : (2 : F) ≠ 0) : StatedSp 2 F :=
  ofSymplecticMat yMat (yMat_symp h2)

theorem mat_yEl (h2 : (2 : F) ≠ 0) : mat 2 F (yEl h2) = yMat := rfl

theorem yEl_mem_planeGroup (h2 : (2 : F) ≠ 0) :
    yEl h2 ∈ planeGroup (Submodule.span F {(uV : Fin 2 ⊕ Fin 2 → F), wV}) := by
  rw [planeGroup, mem_fixing]
  intro v hv
  obtain ⟨h1, h3⟩ := mem_orthSet_span_pair.mp hv
  rw [form_v_uV] at h1
  rw [form_v_wV] at h3
  have h2' : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  have h4 : v (Sum.inl 0) + v (Sum.inr 1) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h2'
    · exact h
  have h5 : v (Sum.inl 1) = v (Sum.inr 0) := sub_eq_zero.mp h1
  rw [mat_yEl]
  ext a
  rcases a with i | i <;> fin_cases i <;>
    simp [yMat, rotM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  all_goals
    rw [show v (Sum.inr 1) = - v (Sum.inl 0) by linear_combination h4, ← h5]
    field_simp
    ring

theorem yMat_sq_apply (h2 : (2 : F) ≠ 0) :
    (yMat * yMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inr 1) = -1 := by
  simp [yMat, rotM, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  field_simp
  ring

theorem yMat_pow_four (h2 : (2 : F) ≠ 0) :
    (yMat * yMat) * (yMat * yMat) = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [yMat, rotM, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  all_goals
    field_simp
    ring

end CFSG.ClassicalInvolution.Asc77.C25I.Sp5
