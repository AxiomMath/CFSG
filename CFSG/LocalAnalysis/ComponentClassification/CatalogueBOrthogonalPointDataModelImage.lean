module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataPlusImage

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.Assembly.LowTwoRank
open CatalogueBOrthogonalSemilinear CatalogueBStabilizerFamily
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_model_normalizer_realization)

section Coordinate

variable {H : Type} [Group H] {n p f : ℕ}

theorem coordinate_odd_family_eq_matrixImage
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    projectivePointFamilyAut (coordinateQuadOdd n K) =
      matrixProjectiveImage (coordinateQuadOdd n K) := by
  obtain ⟨_, ha, _⟩ := coordinate_model_intrinsic_odd h K hK e
  exact pointFamily_eq_matrixImage_of_normalizer _ ha.1 ha.2.1
    (orthogonal_geometry_model_normalizer_realization H .POmegaOdd (.inl rfl) n p f h K hK e).1

theorem coordinate_odd_familyOuter_thirdDerived
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    derivedSeries (familyOuter (projectivePointAction (coordinateQuadOdd n K))) 3 = ⊥ := by
  obtain ⟨hQ, ha, _⟩ := coordinate_model_intrinsic_odd h K hK e
  exact pointFamilyOuter_thirdDerived _ hQ ha.1 ha.2.1
    (orthogonal_geometry_model_normalizer_realization H .POmegaOdd (.inl rfl) n p f h K hK e).1

theorem coordinate_odd_family_similarity
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    (alpha : projectivePointFamilyAut (coordinateQuadOdd n K)) :
    ∃ g : similarityPairs (coordinateQuadOdd n K),
      matrixProjectiveConjugationHom (coordinateQuadOdd n K) g = alpha.val :=
  (SetLike.ext_iff.mp (coordinate_odd_family_eq_matrixImage h K hK e) alpha.val).mp
    alpha.property

theorem coordinate_odd_familyOuter_solvable
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    Group.IsSolvable (familyOuter (projectivePointAction (coordinateQuadOdd n K))) :=
  ⟨⟨3, coordinate_odd_familyOuter_thirdDerived h K hK e⟩⟩

theorem coordinate_minus_family_eq_matrixImage
    (h : StatedClassicalModel H .POmegaMinus n p f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    projectivePointFamilyAut (coordinateQuadMinus n K hn b c) =
      matrixProjectiveImage (coordinateQuadMinus n K hn b c) := by
  obtain ⟨_, ha, _⟩ := coordinate_model_intrinsic_minus h K hK b c hirr e
  exact pointFamily_eq_matrixImage_of_normalizer _ ha.1 ha.2.1
    (orthogonal_geometry_model_normalizer_realization H .POmegaMinus (.inr (.inr rfl)) n p f h
      hn K hK b c hirr e).1

theorem coordinate_minus_familyOuter_thirdDerived
    (h : StatedClassicalModel H .POmegaMinus n p f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    derivedSeries (familyOuter (projectivePointAction (coordinateQuadMinus n K hn b c))) 3 =
      ⊥ := by
  obtain ⟨hQ, ha, _⟩ := coordinate_model_intrinsic_minus h K hK b c hirr e
  exact pointFamilyOuter_thirdDerived _ hQ ha.1 ha.2.1
    (orthogonal_geometry_model_normalizer_realization H .POmegaMinus (.inr (.inr rfl)) n p f h
      hn K hK b c hirr e).1

theorem coordinate_minus_family_similarity
    (h : StatedClassicalModel H .POmegaMinus n p f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    (alpha : projectivePointFamilyAut (coordinateQuadMinus n K hn b c)) :
    ∃ g : similarityPairs (coordinateQuadMinus n K hn b c),
      matrixProjectiveConjugationHom (coordinateQuadMinus n K hn b c) g = alpha.val :=
  (SetLike.ext_iff.mp (coordinate_minus_family_eq_matrixImage h hn K hK b c hirr e)
    alpha.val).mp alpha.property

theorem coordinate_minus_familyOuter_solvable
    (h : StatedClassicalModel H .POmegaMinus n p f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    Group.IsSolvable (familyOuter (projectivePointAction (coordinateQuadMinus n K hn b c))) :=
  ⟨⟨3, coordinate_minus_familyOuter_thirdDerived h hn K hK b c hirr e⟩⟩

end Coordinate


theorem orthogonal_geometry_model_stabilizer_preserving_image (H : Type) [Group H]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel H t n p f) :
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        H ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
          projectivePointFamilyAut (coordinateQuadOdd n K) =
              matrixProjectiveImage (coordinateQuadOdd n K) ∧
            derivedSeries (familyOuter (projectivePointAction (coordinateQuadOdd n K))) 3 = ⊥
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        H ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
          projectivePointFamilyAut (coordinateQuadPlus n K) =
              matrixProjectiveImage (coordinateQuadPlus n K) ∧
            derivedSeries (familyOuter (projectivePointAction (coordinateQuadPlus n K))) 3 = ⊥
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
          projectivePointFamilyAut (coordinateQuadMinus n K hn b c) =
              matrixProjectiveImage (coordinateQuadMinus n K hn b c) ∧
            derivedSeries
                (familyOuter (projectivePointAction (coordinateQuadMinus n K hn b c))) 3 = ⊥
    | _ => False := by
  rcases ht with rfl | rfl | rfl
  · intro K _ _ hK e
    exact ⟨coordinate_odd_family_eq_matrixImage h K hK e,
      coordinate_odd_familyOuter_thirdDerived h K hK e⟩
  · intro K _ _ hK e
    exact orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e
  · intro hn K _ _ hK b c hirr e
    exact ⟨coordinate_minus_family_eq_matrixImage h hn K hK b c hirr e,
      coordinate_minus_familyOuter_thirdDerived h hn K hK b c hirr e⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
