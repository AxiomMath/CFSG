module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSpin

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer

variable {K : Type} [Field K] {b c : K}

abbrev reIdx (K : Type) [Field K] :
    (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
  reindexVectorEquiv (minusIndexEquiv 4 one_le_four')

theorem qM_reIdx (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :
    qM K b c (reIdx K v) = quadMinus 4 K b c v :=
  reindexQuadraticForm_map _ _ v

theorem polar_qM_reIdx (u v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :
    polar (qM K b c) (reIdx K u) (reIdx K v) = polar (quadMinus 4 K b c) u v := by
  rw [polar, polar, ← map_add, qM_reIdx, qM_reIdx, qM_reIdx]

theorem reIdx_reflect (v w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :
    reIdx K (reflect (quadMinus 4 K b c) v w) = reflect (qM K b c) (reIdx K v) (reIdx K w) := by
  by_cases hv : quadMinus 4 K b c v = 0
  · rw [reflect_of_map_eq_zero hv, reflect_of_map_eq_zero (by rw [qM_reIdx, hv])]
    rfl
  · rw [reflect_apply hv, reflect_apply (by rw [qM_reIdx]; exact hv), map_sub, map_smul,
      polar_qM_reIdx, qM_reIdx]

theorem theta_spin {L : Type} [Group L] [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hQ0 : ∃ v, qM K b c v ≠ 0)
    (s : spinGroup (quadMinus 4 K b c)) (g : orthogonalDerived (qM K b c))
    (hg : ∀ v, g.val.val (reIdx K v) = reIdx K (spinAction _ s v)) :
    thetaOf φ hQ0 (φ.symm (spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) s)) =
      QuotientGroup.mk' ((scalarSigns (qM K b c)).subgroupOf (orthogonalDerived (qM K b c))) g := by
  set A : StatedOmega (StatedQuadMinus 4 K b c) :=
    ⟨spinMatrix _ s, spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadMinus (le_refl 4) hirr) s⟩
  have hs : spinToStatedProj (quadMinus 4 K b c) (range_spinMatrix_quadMinus (le_refl 4) hirr) s
      = QuotientGroup.mk' _ A := spinToStatedProj_apply _ _ s
  change projectiveEquiv _ hQ0 (statedProjectiveReindexEquiv (minusIndexEquiv 4 one_le_four')
    (quadMinus 4 K b c) (coe_quadMinus 4 K b c) (φ (φ.symm _))) = _
  rw [MulEquiv.apply_symm_apply, hs, statedProjectiveReindexEquiv_mk]
  apply projectiveEquiv_mk_of_val
  refine LinearEquiv.ext fun w => ?_
  obtain ⟨v, rfl⟩ := (reIdx K).surjective w
  rw [hg, matrixLinearIso_apply_eq, statedDerivedReindexEquiv_vector]
  change reIdx K _ = reIdx K _
  rw [toLinEquiv_spinMatrix]

theorem theta_pairElt {L : Type} [Group L] [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : L ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) (hQ0 : ∃ v, qM K b c v ≠ 0)
    {u₁ u₂ : Fin (2 * 4) → K} (h : quadMinus 4 K b c ((reIdx K).symm u₁) *
      quadMinus 4 K b c ((reIdx K).symm u₂) = 1) (g : orthogonalDerived (qM K b c))
    (hg : g.val.val = reflect (qM K b c) u₁ * reflect (qM K b c) u₂) :
    thetaOf φ hQ0 (φ.symm (spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) (pairElt _ _ h))) =
      QuotientGroup.mk' ((scalarSigns (qM K b c)).subgroupOf (orthogonalDerived (qM K b c))) g := by
  apply theta_spin hirr φ hQ0
  intro v
  rw [hg, spinAction_pairElt, LinearEquiv.mul_apply, LinearEquiv.mul_apply, reIdx_reflect,
    reIdx_reflect, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end CFSG.ComponentClassification.GSThmB.Cent516
