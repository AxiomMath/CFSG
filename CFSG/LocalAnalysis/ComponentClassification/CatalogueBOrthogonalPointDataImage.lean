module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearOuterImageBound

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction
open CatalogueBOrthogonalSemilinearOuterImage CatalogueBStabilizerFamily

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem pointFamily_eq_matrixImage_of_normalizer (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    projectivePointFamilyAut Q = matrixProjectiveImage Q := by
  apply le_antisymm
  · intro α hα
    let a : projectivePointFamilyAut Q := ⟨α, hα⟩
    have hp : pointFamilyNormalizerEquiv Q hρ hs a ∈
        (similarityPointImage Q).subgroupOf (projectivePointNormalizer Q) := by
      change (pointFamilyNormalizerEquiv Q hρ hs a).val ∈ similarityPointImage Q
      rw [← hN]
      exact (pointFamilyNormalizerEquiv Q hρ hs a).property
    rw [← pointFamilyNormalizerEquiv_similarity_image Q hρ hs] at hp
    obtain ⟨β, hβ, hβα⟩ := hp
    have hb : β = a := (pointFamilyNormalizerEquiv Q hρ hs).injective hβα
    change a ∈ (matrixProjectiveImage Q).subgroupOf (projectivePointFamilyAut Q)
    exact hb ▸ hβ
  · exact projective_image_le_pointFamilyAut Q

@[expose] def pointFamilyMatrixImageEquiv (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    projectivePointFamilyAut Q ≃* matrixProjectiveImage Q :=
  MulEquiv.subgroupCongr (pointFamily_eq_matrixImage_of_normalizer Q hρ hs hN)

theorem pointFamilyMatrixImageEquiv_val (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q)
    (α : projectivePointFamilyAut Q) :
    (pointFamilyMatrixImageEquiv Q hρ hs hN α).val = α.val := rfl

theorem pointFamilyMatrixImageEquiv_inner (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    (familyInner (projectivePointAction Q)).map
        (pointFamilyMatrixImageEquiv Q hρ hs hN).toMonoidHom = matrixImageInner Q := by
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact hβ
  · intro hα
    refine ⟨(pointFamilyMatrixImageEquiv Q hρ hs hN).symm α, ?_,
      (pointFamilyMatrixImageEquiv Q hρ hs hN).apply_symm_apply α⟩
    exact hα

@[expose] def pointFamilyMatrixOuterEquiv (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    familyOuter (projectivePointAction Q) ≃* MatrixImageInnerQuotient Q := by
  letI : (familyInner (projectivePointAction Q)).Normal :=
    familyInnerNormal (projectivePointAction Q)
  exact QuotientGroup.congr _ _ (pointFamilyMatrixImageEquiv Q hρ hs hN)
    (pointFamilyMatrixImageEquiv_inner Q hρ hs hN)

theorem pointFamilyMatrixOuterEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q)
    (α : projectivePointFamilyAut Q) :
    pointFamilyMatrixOuterEquiv Q hρ hs hN
        ((QuotientGroup.mk' (familyInner (projectivePointAction Q))) α) =
      matrixImageInnerProjection Q (pointFamilyMatrixImageEquiv Q hρ hs hN α) :=
  by
    let : (familyInner (projectivePointAction Q)).Normal :=
      familyInnerNormal (projectivePointAction Q)
    exact QuotientGroup.congr_mk' (familyInner (projectivePointAction Q))
      (matrixImageInner Q) (pointFamilyMatrixImageEquiv Q hρ hs hN)
      (pointFamilyMatrixImageEquiv_inner Q hρ hs hN) α

theorem pointFamilyOuter_thirdDerived [Finite K] (Q : QuadraticForm K (Fin d → K))
    (hQ : Q ≠ 0) (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    derivedSeries (familyOuter (projectivePointAction Q)) 3 = ⊥ := by
  have h := map_derivedSeries_eq (pointFamilyMatrixOuterEquiv Q hρ hs hN).symm.surjective 3
  rw [matrixImageInnerQuotient_thirdDerived Q hQ, Subgroup.map_bot] at h
  exact h.symm

theorem pointFamilyOuter_solvable [Finite K] (Q : QuadraticForm K (Fin d → K))
    (hQ : Q ≠ 0) (hρ : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (hN : projectivePointNormalizer Q = similarityPointImage Q) :
    Group.IsSolvable (familyOuter (projectivePointAction Q)) :=
  ⟨⟨3, pointFamilyOuter_thirdDerived Q hQ hρ hs hN⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
