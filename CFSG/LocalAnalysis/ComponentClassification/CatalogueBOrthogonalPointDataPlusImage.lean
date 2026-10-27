module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelIntrinsic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealizationModels

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalSemilinearOuterImage
open CatalogueBStabilizerFamily

variable {H : Type} [Group H] {n p f : ℕ}

theorem coordinate_plus_family_eq_matrixImage
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    projectivePointFamilyAut (coordinateQuadPlus n K) =
      matrixProjectiveImage (coordinateQuadPlus n K) := by
  obtain ⟨_, ha, _⟩ := coordinate_model_intrinsic_plus h K hK e
  exact pointFamily_eq_matrixImage_of_normalizer _ ha.1 ha.2.1
    (CatalogueBOrthogonalPointPlusNormalizerRealization.model_plus_projective_normalizer_eq
      h K hK e)

theorem coordinate_plus_familyOuter_thirdDerived
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    derivedSeries (familyOuter (projectivePointAction (coordinateQuadPlus n K))) 3 = ⊥ := by
  obtain ⟨hQ, ha, _⟩ := coordinate_model_intrinsic_plus h K hK e
  exact pointFamilyOuter_thirdDerived _ hQ ha.1 ha.2.1
    (CatalogueBOrthogonalPointPlusNormalizerRealization.model_plus_projective_normalizer_eq
      h K hK e)

theorem coordinate_plus_family_similarity
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (alpha : projectivePointFamilyAut (coordinateQuadPlus n K)) :
    ∃ g : similarityPairs (coordinateQuadPlus n K),
      matrixProjectiveConjugationHom (coordinateQuadPlus n K) g = alpha.val := by
  exact (SetLike.ext_iff.mp (coordinate_plus_family_eq_matrixImage h K hK e)
    alpha.val).mp alpha.property

theorem orthogonal_geometry_plus_model_stabilizer_preserving_image
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    projectivePointFamilyAut (coordinateQuadPlus n K) =
        matrixProjectiveImage (coordinateQuadPlus n K) ∧
      derivedSeries (familyOuter (projectivePointAction (coordinateQuadPlus n K))) 3 = ⊥ :=
  ⟨coordinate_plus_family_eq_matrixImage h K hK e,
    coordinate_plus_familyOuter_thirdDerived h K hK e⟩

theorem coordinate_plus_familyOuter_solvable
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    Group.IsSolvable (familyOuter (projectivePointAction (coordinateQuadPlus n K))) :=
  ⟨⟨3, coordinate_plus_familyOuter_thirdDerived h K hK e⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
