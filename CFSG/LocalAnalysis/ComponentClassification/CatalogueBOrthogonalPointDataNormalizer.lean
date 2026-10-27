module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointAction
open CatalogueBStabilizerFamily

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def projectivePointNormalizer (Q : QuadraticForm K (Fin d → K)) :
    Subgroup (Equiv.Perm (Points Q)) := imageNormalizer (projectivePointAction Q)

@[expose] def pointFamilyNormalizerEquiv (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    projectivePointFamilyAut Q ≃* projectivePointNormalizer Q :=
  normalizerEquiv (projectivePointAction Q) hrho hs

theorem pointFamilyNormalizerEquiv_unique (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (alpha : projectivePointFamilyAut Q) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L, (projectivePointStabilizer Q L).map alpha.val.toMonoidHom =
      projectivePointStabilizer Q (phi L)) :
    phi = (pointFamilyNormalizerEquiv Q hrho hs alpha).val :=
  pointPerm_unique (projectivePointAction Q) hs alpha phi hphi

theorem pointFamilyNormalizerEquiv_stabilizer (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (alpha : projectivePointFamilyAut Q) (L : Points Q) :
    (projectivePointStabilizer Q L).map alpha.val.toMonoidHom =
      projectivePointStabilizer Q ((pointFamilyNormalizerEquiv Q hrho hs alpha).val L) :=
  normalizerEquiv_stabilizer (projectivePointAction Q) hrho hs alpha L

theorem pointFamilyNormalizerEquiv_covariance (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (alpha : projectivePointFamilyAut Q) (x : matrixProjectiveDerived Q) :
    (pointFamilyNormalizerEquiv Q hrho hs alpha).val * projectivePointAction Q x *
        (pointFamilyNormalizerEquiv Q hrho hs alpha).val⁻¹ =
      projectivePointAction Q (alpha.val x) :=
  normalizerEquiv_covariance (projectivePointAction Q) hrho hs alpha x

theorem pointFamilyNormalizerEquiv_similarity (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) (g : similarityPairs Q) :
    (pointFamilyNormalizerEquiv Q hrho hs
      ⟨matrixProjectiveConjugationHom Q g,
        projective_image_le_pointFamilyAut Q ⟨g, rfl⟩⟩).val =
      similarityPointAction Q g :=
  pointPerm_of_covariance (projectivePointAction Q) hs (matrixProjectiveConjugationHom Q g)
    (similarityPointAction Q g) (similarity_projective_covariance Q g)

theorem pointFamilyNormalizerEquiv_inner_image (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    (familyInner (projectivePointAction Q)).map
        (pointFamilyNormalizerEquiv Q hrho hs).toMonoidHom =
      normalizerImage (projectivePointAction Q) :=
  normalizerEquiv_inner_image (projectivePointAction Q) hrho hs

theorem pointFamilyNormalizerEquiv_similarity_image (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    ((matrixProjectiveImage Q).subgroupOf (projectivePointFamilyAut Q)).map
        (pointFamilyNormalizerEquiv Q hrho hs).toMonoidHom =
      (similarityPointImage Q).subgroupOf (projectivePointNormalizer Q) :=
  compatible_image (projectivePointAction Q) hrho hs (matrixProjectiveConjugationHom Q)
    (similarityPointAction Q) (similarity_projective_covariance Q)

@[expose] def pointFamilyOuterEquiv (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    familyOuter (projectivePointAction Q) ≃* normalizerOuter (projectivePointAction Q) :=
  quotientEquiv (projectivePointAction Q) hrho hs

theorem pointFamilyOuterEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q))
    (alpha : projectivePointFamilyAut Q) :
    pointFamilyOuterEquiv Q hrho hs
        ((QuotientGroup.mk' (familyInner (projectivePointAction Q))) alpha) =
      (QuotientGroup.mk' (normalizerImage (projectivePointAction Q)))
        (pointFamilyNormalizerEquiv Q hrho hs alpha) :=
  quotientEquiv_mk (projectivePointAction Q) hrho hs alpha

theorem orthogonal_geometry_stabilizer_family_normalizer (hd : 1 ≤ d)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hrho : Function.Injective (projectivePointAction Q))
    (hs : Function.Injective (projectivePointStabilizer Q)) :
    (∀ (alpha : projectivePointFamilyAut Q) (L : Points Q),
      (projectivePointStabilizer Q L).map alpha.val.toMonoidHom =
        projectivePointStabilizer Q ((pointFamilyNormalizerEquiv Q hrho hs alpha).val L)) ∧
    (∀ (alpha : projectivePointFamilyAut Q) (x : matrixProjectiveDerived Q),
      (pointFamilyNormalizerEquiv Q hrho hs alpha).val * projectivePointAction Q x *
          (pointFamilyNormalizerEquiv Q hrho hs alpha).val⁻¹ =
        projectivePointAction Q (alpha.val x)) ∧
    (familyInner (projectivePointAction Q)).map
        (pointFamilyNormalizerEquiv Q hrho hs).toMonoidHom =
      normalizerImage (projectivePointAction Q) ∧
    ((matrixProjectiveImage Q).subgroupOf (projectivePointFamilyAut Q)).map
        (pointFamilyNormalizerEquiv Q hrho hs).toMonoidHom =
      (similarityPointImage Q).subgroupOf (projectivePointNormalizer Q) ∧
    Nonempty (familyOuter (projectivePointAction Q) ≃*
      normalizerOuter (projectivePointAction Q)) := by
  have _hd := hd
  have _hQ := hQ
  exact ⟨pointFamilyNormalizerEquiv_stabilizer Q hrho hs,
    pointFamilyNormalizerEquiv_covariance Q hrho hs,
    pointFamilyNormalizerEquiv_inner_image Q hrho hs,
    pointFamilyNormalizerEquiv_similarity_image Q hrho hs, ⟨pointFamilyOuterEquiv Q hrho hs⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
