module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowSpinMatrix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus polar_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv reindexMatrixEquiv reindexMatrixEquiv_mulVec reindexQuadraticForm_map
  plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv_val)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mulVec_of_charTwo)

section Symmetry

variable {k : Type} [Field k]

theorem plusSwapMat_mulVec (y : Fin 4 ⊕ Fin 4 → k) :
    (plusSwapMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ y = y ∘ plusSwap3 := by
  rw [plusSwapMat, PEquiv.toMatrix_toPEquiv_mulVec]

theorem polar_quadPlus_omegaPlusVec (y : Fin 4 ⊕ Fin 4 → k) :
    polar (quadPlus 4 k) (omegaPlusVec k) y = y (Sum.inl 3) + y (Sum.inr 3) := by
  rw [polar_quadPlus, Fin.sum_univ_four]
  simp only [omegaPlusVec_inl, omegaPlusVec_inr]
  simp only [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
    show (2 : Fin 4) ≠ 3 by decide, ite_false, ite_true, zero_mul, mul_zero, add_zero, zero_add,
    one_mul, mul_one]
  ring

variable [CharP k 2]

theorem plusSwapMat_mulVec_eq (y : Fin 4 ⊕ Fin 4 → k) :
    (plusSwapMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) *ᵥ y =
      y + polar (quadPlus 4 k) (omegaPlusVec k) y • omegaPlusVec k := by
  rw [plusSwapMat_mulVec, polar_quadPlus_omegaPlusVec]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  funext i
  rcases i with i | i <;> fin_cases i
  all_goals
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, omegaPlusVec_inl,
      omegaPlusVec_inr, plusSwap3]
  all_goals simp [Equiv.swap_apply_of_ne_of_ne]
  · linear_combination (-y (Sum.inl 3)) * h2
  · linear_combination (-y (Sum.inr 3)) * h2

end Symmetry

section Reindex

variable {ι : Type} {K : Type} [Field K] {d : ℕ}

omit [Field K] in
theorem polar_reindexQuadraticForm [Field K] (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K))
    (v w : ι → K) :
    polar (reindexQuadraticForm e Q) (reindexVectorEquiv e v) (reindexVectorEquiv e w) =
      polar Q v w := by
  simp only [QuadraticMap.polar, ← map_add, reindexQuadraticForm_map]

variable {k : Type} [Field k] [CharP k 2]

theorem reindexMatrixEquiv_plusSwapGL :
    reindexMatrixEquiv (plusIndexEquiv 4) (plusSwapGL (K := k)) =
      symmetryGL (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k))
        (reindexVectorEquiv (plusIndexEquiv 4) (omegaPlusVec k)) := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨y, rfl⟩ := (reindexVectorEquiv (K := k) (plusIndexEquiv 4)).surjective x
  rw [symmetryGL_mulVec_of_charTwo (reindexQuadraticForm_plus_omegaPlusVec k),
    polar_reindexQuadraticForm]
  have h1 := reindexMatrixEquiv_mulVec (plusIndexEquiv 4) (plusSwapGL (K := k)) y
  rw [matrixLinearEquiv_apply] at h1
  rw [h1, ← map_smul, ← map_add]
  congr 1
  exact plusSwapMat_mulVec_eq y

end Reindex

section BetaC

variable {k : Type} [Field k] [CharP k 2]

theorem coe_omegaPlusBetaC (A : StatedOmega (StatedQuadPlus 4 k)) :
    ((omegaPlusBetaC k A : StatedOmega (StatedQuadPlus 4 k)) : GL (Fin 4 ⊕ Fin 4) k) =
      plusSwapGL * (A : GL (Fin 4 ⊕ Fin 4) k) * plusSwapGL⁻¹ := by
  set Q' := reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 k) with hQ'
  have h := matrixDerivedScalars_omegaPlus_eq_bot k
  have key := omegaProjEquiv_omegaSymmetryAut (plusIndexEquiv 4) (quadPlus 4 k)
    (coe_quadPlus 4 k) h (omegaPlusVec k) A
  rw [omegaProjEquiv_apply, omegaProjEquiv_apply] at key
  change _ = matrixProjectiveConjugation Q' _ (matrixProjectiveProjection Q' _) at key
  rw [matrixProjectiveConjugation_mk, (matrixProjectiveProjection_injective h).eq_iff] at key
  have key2 := congrArg Subtype.val key
  rw [statedDerivedReindexEquiv_val, matrixDerivedConjugation_val, matrixIsometryInclusion_val,
    statedDerivedReindexEquiv_val] at key2
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
    MulAut.one_apply] at key2
  apply (reindexMatrixEquiv (K := k) (plusIndexEquiv 4)).injective
  change reindexMatrixEquiv (plusIndexEquiv 4)
    ((omegaSymmetryAut (plusIndexEquiv 4) (quadPlus 4 k) (coe_quadPlus 4 k) h (omegaPlusVec k) A :
      StatedOmega (StatedQuadPlus 4 k)) : GL (Fin 4 ⊕ Fin 4) k) = _
  rw [key2, map_mul, map_mul, map_inv, reindexMatrixEquiv_plusSwapGL]

end BetaC

section Spin

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem omegaPlusBetaC_eq_plusSwapOmegaAut : omegaPlusBetaC K = plusSwapOmegaAut := by
  ext A
  rw [coe_omegaPlusBetaC, coe_plusSwapOmegaAut]

theorem spinOmegaEquiv_spinD4Graph_eq_omegaPlusBetaC (x : spinGroup (quadPlus 4 K)) :
    spinOmegaEquiv (spinD4Graph K x) = omegaPlusBetaC K (spinOmegaEquiv x) := by
  rw [spinOmegaEquiv_spinD4Graph, omegaPlusBetaC_eq_plusSwapOmegaAut]

end Spin

end CFSG.SeitzReduction.F4Pilot
