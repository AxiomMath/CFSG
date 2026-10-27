module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataWitnessOuterBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataPlusImage

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalPointModelNormalizer CatalogueBStabilizerFamily

variable {H : Type} [Group H] {n p f : ℕ}

@[expose] def coordinate_plus_familyOuter_witness_equiv
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    familyOuter ((projectivePointAction (coordinateQuadPlus n K)).comp
        (coordinatePlusWitnessEquiv K e).toMonoidHom) ≃*
      familyOuter (projectivePointAction (coordinateQuadPlus n K)) := by
  obtain ⟨_, ha, hH⟩ := coordinate_model_intrinsic_plus h K hK e
  exact familyOuterRangeEquiv _ _
    (action_range_comp_equiv _ _ (coordinatePlusWitnessEquiv K e))
    hH.1 hH.2.1 ha.1 ha.2.1

@[expose] def coordinate_odd_familyOuter_witness_equiv
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    familyOuter ((projectivePointAction (coordinateQuadOdd n K)).comp
        (coordinateOddWitnessEquiv K e).toMonoidHom) ≃*
      familyOuter (projectivePointAction (coordinateQuadOdd n K)) := by
  obtain ⟨_, ha, hH⟩ := coordinate_model_intrinsic_odd h K hK e
  exact familyOuterRangeEquiv _ _
    (action_range_comp_equiv _ _ (coordinateOddWitnessEquiv K e))
    hH.1 hH.2.1 ha.1 ha.2.1

@[expose] def coordinate_minus_familyOuter_witness_equiv
    (h : StatedClassicalModel H .POmegaMinus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    familyOuter ((projectivePointAction
        (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)).comp
        (coordinateMinusWitnessEquiv K (by have := h.1.2.2; omega) b c e).toMonoidHom) ≃*
      familyOuter (projectivePointAction
        (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)) := by
  obtain ⟨_, ha, hH⟩ := coordinate_model_intrinsic_minus h K hK b c hirr e
  exact familyOuterRangeEquiv _ _
    (action_range_comp_equiv _ _
      (coordinateMinusWitnessEquiv K (by have := h.1.2.2; omega) b c e))
    hH.1 hH.2.1 ha.1 ha.2.1

theorem coordinate_plus_familyOuter_witness_thirdDerived
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    derivedSeries (familyOuter ((projectivePointAction (coordinateQuadPlus n K)).comp
      (coordinatePlusWitnessEquiv K e).toMonoidHom)) 3 = ⊥ := by
  have he := map_derivedSeries_eq
    (f := (coordinate_plus_familyOuter_witness_equiv h K hK e).symm.toMonoidHom)
    (coordinate_plus_familyOuter_witness_equiv h K hK e).symm.surjective 3
  rw [coordinate_plus_familyOuter_thirdDerived h K hK e, Subgroup.map_bot] at he
  exact he.symm

theorem coordinate_plus_familyOuter_witness_solvable
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    Group.IsSolvable (familyOuter ((projectivePointAction (coordinateQuadPlus n K)).comp
      (coordinatePlusWitnessEquiv K e).toMonoidHom)) :=
  ⟨⟨3, coordinate_plus_familyOuter_witness_thirdDerived h K hK e⟩⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
