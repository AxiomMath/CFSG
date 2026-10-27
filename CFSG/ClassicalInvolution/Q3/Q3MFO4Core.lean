module

public import CFSG.ClassicalInvolution.Q3.Q3MFO4Mat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.ClassicalInvolution.Asc77.AscCX9X1
public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4 CFSG.ClassicalInvolution.Asc77.CX.MF2L
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Field3

variable {F : Type} [Field F] [Finite F]

theorem eq_zero_or_one_or_neg_one_of_card (hF : Nat.card F = 3) (x : F) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h := FiniteField.pow_card x
  rw [hc] at h
  have h3 : x * (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

theorem two_ne_zero_of_card (hF : Nat.card F = 3) : (2 : F) ≠ 0 :=
  two_ne_zero_of_odd_natCard (by rw [hF]; decide)

theorem ringEquiv_eq_refl (hF : Nat.card F = 3) (σ : F ≃+* F) : σ = RingEquiv.refl F := by
  ext x
  rcases eq_zero_or_one_or_neg_one_of_card hF x with rfl | rfl | rfl <;> simp

end Field3

section CoreZero

variable {F : Type} [Field F] [Finite F]

theorem core_zero (hF : Nat.card F = 3) (A : GL (Fin 4) F)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      conjAut 4 F A (proj 4 F r) = proj 4 F r)
    (hsq : conjAut 4 F A * conjAut 4 F A = 1) : A * A = 1 := by
  have h2 := two_ne_zero_of_card hF
  have h4 := four_ne_zero h2
  have r01 := exact_rel_conj h4 A (hfix _ (u01_mem 1)) (trace_E01 1)
  have r10 := exact_rel_conj h4 A (hfix _ (u10_mem 1)) (trace_E10 1)
  obtain ⟨m01, m02, m03, -, -, -, -, -, -, -, -⟩ := shape_comm r01 r10
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) (A * A) 1
    (by rw [map_mul, hsq, map_one, mul_one])
  have hcm : ((A * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hc, smul_one_eq_diagonal]
    rfl
  have h00 : (A : Matrix (Fin 4) (Fin 4) F) 0 0 * (A : Matrix (Fin 4) (Fin 4) F) 0 0 = c := by
    have h := congrFun (congrFun hcm 0) 0
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [m01, m02, m03] at h
    linear_combination h
  have hc1 : (c : F) = 1 := by
    rcases eq_zero_or_one_or_neg_one_of_card hF ((A : Matrix (Fin 4) (Fin 4) F) 0 0) with
      h | h | h
    · exact absurd (by rw [← h00, h, mul_zero]) c.ne_zero
    · rw [← h00, h, mul_one]
    · rw [← h00, h]; ring
  apply Units.ext
  rw [hcm, hc1, one_smul]
  rfl

end CoreZero

section CoreOne

variable {F : Type} [Field F] [Finite F]

theorem core_one (hF : Nat.card F = 3) (A : GL (Fin 4) F)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      (conjAut 4 F A * dualAut 4 F) (proj 4 F r) = proj 4 F r)
    (hsq : (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F A * dualAut 4 F) = 1) :
    ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧ (A : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  have h2 := two_ne_zero_of_card hF
  have h4 := four_ne_zero h2
  have hσ1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
  have hfix' : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      (conjAut 4 F A * fieldAut 4 F (RingEquiv.refl F) * dualAut 4 F) (proj 4 F r) =
        proj 4 F r := by
    intro r hr
    rw [hσ1, mul_one]
    exact hfix r hr
  have r01 := exact_rel_one h4 A (RingEquiv.refl F) (hfix' _ (u01_mem 1)) (trace_E01 1)
    (by rw [coe_inv_transpose_u01, map_E10, trace_E10])
  have r10 := exact_rel_one h4 A (RingEquiv.refl F) (hfix' _ (u10_mem 1)) (trace_E10 1)
    (by rw [coe_inv_transpose_u10, map_E01, trace_E01])
  rw [show ((u01 (1 : F) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E01 1 from rfl,
    coe_inv_transpose_u01, map_E10] at r01
  rw [show ((u10 (1 : F) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E10 1 from rfl,
    coe_inv_transpose_u10, map_E01] at r10
  have hs := shape_anti (M := (A : Matrix (Fin 4) (Fin 4) F)) (by simpa using r01)
    (by simpa using r10)
  have hsq2 : (conjAut 4 F A * fieldAut 4 F (RingEquiv.refl F) * dualAut 4 F) ^ 2 = 1 := by
    rw [hσ1, mul_one, sq]
    exact hsq
  rw [sq_conjAut_fieldAut_dualAut] at hsq2
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq2
  have hmap : ∀ X : GL (Fin 4) F, ((GeneralLinearGroup.map
      ((RingEquiv.refl F : F ≃+* F) : F →+* F) X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (X : Matrix (Fin 4) (Fin 4) F) := fun X => by
    ext i j
    rfl
  have hcm : (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    have h := congrArg (fun X : GL (Fin 4) F => (X : Matrix (Fin 4) (Fin 4) F)) hc
    rw [Units.val_mul, hmap, GeneralLinearGroup.coe_inverseTranspose] at h
    rw [← h, smul_one_eq_diagonal]
    rfl
  have hNA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
  have hA : (A : Matrix (Fin 4) (Fin 4) F) = (c : F) • (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    calc (A : Matrix (Fin 4) (Fin 4) F)
        = (A : Matrix (Fin 4) (Fin 4) F) * (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
            (A : Matrix (Fin 4) (Fin 4) F)ᵀ) := by rw [hNA, Matrix.mul_one]
      _ = ((c : F) • (1 : Matrix (Fin 4) (Fin 4) F)) * (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [← Matrix.mul_assoc, ← hcm]
      _ = (c : F) • (A : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [Matrix.smul_mul, Matrix.one_mul]
  exact eq_spForm_of_shape h2 (det_ne_zero A) hs c hA

end CoreOne

end CFSG.ClassicalInvolution.Q3.Q3MFO4
