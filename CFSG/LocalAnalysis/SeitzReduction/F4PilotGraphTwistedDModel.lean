module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinBetaC

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus polar_quadMinus_single_inr_inr_zero)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv reindexMatrixEquiv reindexMatrixEquiv_mulVec minusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv_val)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)

section Symmetry

variable {k : Type} [Field k] [CharP k 2]

theorem minusShearMat_mulVec_eq_symm (b c : k) (y : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    minusShearMat b *ᵥ y = y + polar (quadMinus 4 k b c) (minusVec k) y • minusVec k := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [minusShearMat_mulVec, polar_comm, minusVec, polar_quadMinus_single_inr_inr_zero, h2,
    zero_mul, zero_add]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_apply, Pi.single_apply,
    Pi.zero_apply]
  split_ifs <;> ring

theorem reindexMatrixEquiv_minusShear (b c : k) :
    reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num)) (minusShear b) =
      symmetryGL (reindexQuadraticForm (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c))
        (reindexVectorEquiv (minusIndexEquiv 4 (by norm_num)) (minusVec k)) := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨y, rfl⟩ := (reindexVectorEquiv (K := k) (minusIndexEquiv 4 (by norm_num))).surjective x
  rw [symmetryGL_mulVec_of_charTwo (reindexQuadraticForm_minus_minusVec k),
    polar_reindexQuadraticForm]
  have h1 := reindexMatrixEquiv_mulVec (minusIndexEquiv 4 (by norm_num)) (minusShear (k := k) b) y
  rw [matrixLinearEquiv_apply] at h1
  rw [h1, ← map_smul, ← map_add]
  congr 1
  exact minusShearMat_mulVec_eq_symm b c y

theorem coe_omegaMinusBetaC (b c : k) (A : StatedOmega (StatedQuadMinus 4 k b c)) :
    ((omegaMinusBetaC k b c A : StatedOmega (StatedQuadMinus 4 k b c)) :
      GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
        minusShear b * (A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) * (minusShear b)⁻¹ := by
  set Q' := reindexQuadraticForm (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c) with hQ'
  have h := matrixDerivedScalars_omegaMinus_eq_bot k b c
  have key := omegaProjEquiv_omegaSymmetryAut (minusIndexEquiv 4 (by norm_num))
    (quadMinus 4 k b c) (coe_quadMinus 4 k b c) h (minusVec k) A
  rw [omegaProjEquiv_apply, omegaProjEquiv_apply] at key
  change _ = matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' _) at key
  rw [matrixProjectiveConjugation_mk, (matrixProjectiveProjection_injective h).eq_iff] at key
  have key2 := congrArg Subtype.val key
  rw [statedDerivedReindexEquiv_val, matrixDerivedConjugation_val, matrixIsometryInclusion_val,
    statedDerivedReindexEquiv_val] at key2
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
    MulAut.one_apply] at key2
  apply (reindexMatrixEquiv (K := k) (minusIndexEquiv 4 (by norm_num))).injective
  change reindexMatrixEquiv (minusIndexEquiv 4 (by norm_num))
    ((omegaSymmetryAut (minusIndexEquiv 4 (by norm_num)) (quadMinus 4 k b c)
      (coe_quadMinus 4 k b c) h (minusVec k) A : StatedOmega (StatedQuadMinus 4 k b c)) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) = _
  rw [key2, map_mul, map_mul, map_inv, reindexMatrixEquiv_minusShear b c]

end Symmetry

section Field

variable {k : Type} [Field k] [CharP k 2]

theorem coe_minusShear_inv (s : k) :
    (((minusShear s)⁻¹ : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
      Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
        minusShearMat s :=
  rfl

omit [CharP k 2] in
theorem minusShearMat_mul (s s' : k) :
    minusShearMat s * minusShearMat s' = minusShearMat (s + s') := by
  have hE : minusShearE s * minusShearE s' = 0 := by
    rw [minusShearE, minusShearE]
    exact Matrix.single_mul_single_of_ne (h := w_ne_u) ..
  rw [minusShearMat, minusShearMat, minusShearMat, add_mul, mul_add, mul_add, one_mul, mul_one,
    one_mul, hE, add_zero, minusShearE, minusShearE, minusShearE, Matrix.single_add]
  abel

omit [CharP k 2] in
theorem minusShearMat_map (ρ : k ≃+* k) (s : k) :
    (minusShearMat s).map ρ = minusShearMat (ρ s) := by
  ext i j
  simp only [minusShearMat, minusShearE, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem omegaMinusBetaC_omegaMinusFieldAut (c : k) (ρ : k ≃+* k) (s : k)
    (hs : s ^ 2 + s + c = ρ c) (A : StatedOmega (StatedQuadMinus 4 k 1 c)) :
    omegaMinusBetaC k 1 c (omegaMinusFieldAut k c ρ s hs A) =
      omegaMinusFieldAut k c ρ s hs (omegaMinusBetaC k 1 c A) := by
  set X := ((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) with hX
  have hmap : ∀ M N : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k, (M * N).map ρ = M.map ρ * N.map ρ := fun M N => by
    simp
  have e1 : (((omegaMinusBetaC k 1 c (omegaMinusFieldAut k c ρ s hs A) :
      StatedOmega (StatedQuadMinus 4 k 1 c)) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
      minusShearMat (1 : k) * (minusShearMat s * X.map ρ * minusShearMat s) *
        minusShearMat (1 : k) := by
    rw [coe_omegaMinusBetaC, Units.val_mul, Units.val_mul, coe_minusShear_inv,
      coe_omegaMinusFieldAut]
    rfl
  have e2 : (((omegaMinusFieldAut k c ρ s hs (omegaMinusBetaC k 1 c A) :
      StatedOmega (StatedQuadMinus 4 k 1 c)) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
      minusShearMat s * (minusShearMat (1 : k) * X * minusShearMat (1 : k)).map ρ *
        minusShearMat s := by
    rw [coe_omegaMinusFieldAut, coe_omegaMinusBetaC, Units.val_mul, Units.val_mul,
      coe_minusShear_inv]
    rfl
  apply Subtype.ext
  apply Units.ext
  rw [e1, e2, hmap, hmap, minusShearMat_map, map_one]
  calc minusShearMat (1 : k) * (minusShearMat s * X.map ρ * minusShearMat s) * minusShearMat (1 : k)
      = (minusShearMat (1 : k) * minusShearMat s) * X.map ρ *
          (minusShearMat s * minusShearMat (1 : k)) := by
        simp only [Matrix.mul_assoc]
    _ = (minusShearMat s * minusShearMat (1 : k)) * X.map ρ *
          (minusShearMat (1 : k) * minusShearMat s) := by
        rw [minusShearMat_mul, minusShearMat_mul, add_comm (1 : k) s]
    _ = minusShearMat s * (minusShearMat (1 : k) * X.map ρ * minusShearMat (1 : k)) *
          minusShearMat s := by
        simp only [Matrix.mul_assoc]

end Field

end CFSG.SeitzReduction.F4Pilot
