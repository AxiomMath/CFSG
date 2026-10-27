module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter OuterAutomorphisms

universe u v

@[expose] def coordinateOuterEquivPSL (K : Type u) [Field K] :
    Outer (coordinateG K) ≃* Outer (PSL2 K) :=
  equivalence (pslEquivCoordinateG K).symm

@[expose] def projectiveOuterEquivPSL (K : Type u) [Field K] :
    Outer (ProjectiveQuotient K) ≃* Outer (PSL2 K) :=
  equivalence (projectiveQuotientEquivPSL K)

@[expose] def projectiveOuterEquivCoordinate (K : Type u) [Field K] :
    Outer (ProjectiveQuotient K) ≃* Outer (coordinateG K) :=
  equivalence (projectiveQuotientEquivCoordinateG K)

@[expose] def coordinateToOuter (K : Type u) [Field K] [Finite K] :
    coordinateE K →* Outer (coordinateG K) :=
  (QuotientGroup.mk' (inner (coordinateG K))).comp (coordinateConjugation K)

theorem coordinateToOuter_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (coordinateToOuter K) :=
  (QuotientGroup.mk'_surjective (inner (coordinateG K))).comp
    (coordinateConjugation_surjective K)

theorem coordinateToOuter_ker (K : Type u) [Field K] [Finite K] :
    (coordinateToOuter K).ker = (coordinateG K).subgroupOf (coordinateE K) := by
  ext e
  change (QuotientGroup.mk (coordinateConjugation K e) : Outer (coordinateG K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, ← coordinateConjugation_G_image]
  constructor
  · rintro ⟨d, hd, hde⟩
    exact (coordinateConjugation_injective K hde) ▸ hd
  · intro he
    exact ⟨e, he, rfl⟩

@[expose] def coordinateOuterQuotientEquiv (K : Type u) [Field K] [Finite K] :
    CoordinateQuotientEG K ≃* Outer (coordinateG K) :=
  QuotientGroup.congr ((coordinateG K).subgroupOf (coordinateE K))
    (inner (coordinateG K)) (coordinateConjugationEquiv K)
    (coordinateConjugation_G_image K)

theorem coordinateOuterQuotientEquiv_mk (K : Type u) [Field K] [Finite K]
    (e : coordinateE K) :
    coordinateOuterQuotientEquiv K
      (QuotientGroup.mk' ((coordinateG K).subgroupOf (coordinateE K)) e) =
        coordinateToOuter K e :=
  QuotientGroup.congr_mk' _ _ _ _ e

theorem coordinateOuter_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (coordinateG K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (coordinateOuterQuotientEquiv K).toMonoidHom
    (coordinateOuterQuotientEquiv K).surjective (coordinateEG_secondDerived_eq_bot K)

theorem coordinateOuter_solvable (K : Type u) [Field K] [Finite K] :
    Group.IsSolvable (Outer (coordinateG K)) :=
  ⟨⟨2, coordinateOuter_secondDerived_eq_bot K⟩⟩

theorem projectiveOuter_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (ProjectiveQuotient K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (projectiveOuterEquivCoordinate K).symm.toMonoidHom
    (projectiveOuterEquivCoordinate K).symm.surjective
    (coordinateOuter_secondDerived_eq_bot K)

theorem projectiveOuter_solvable (K : Type u) [Field K] [Finite K] :
    Group.IsSolvable (Outer (ProjectiveQuotient K)) :=
  ⟨⟨2, projectiveOuter_secondDerived_eq_bot K⟩⟩

theorem linear_two_Schreier (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (coordinateG K)) 2 = ⊥ ∧
      derivedSeries (Outer (ProjectiveQuotient K)) 2 = ⊥ ∧
      Group.IsSolvable (Outer (coordinateG K)) ∧
      Group.IsSolvable (Outer (ProjectiveQuotient K)) :=
  ⟨coordinateOuter_secondDerived_eq_bot K, projectiveOuter_secondDerived_eq_bot K,
    coordinateOuter_solvable K, projectiveOuter_solvable K⟩

theorem coordinateOuter_secondDerived_eq_bot_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* coordinateG K) :
    derivedSeries (Outer G) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (equivalence e).symm.toMonoidHom
    (equivalence e).symm.surjective (coordinateOuter_secondDerived_eq_bot K)

theorem coordinateOuter_solvable_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* coordinateG K) :
    Group.IsSolvable (Outer G) :=
  ⟨⟨2, coordinateOuter_secondDerived_eq_bot_of_equiv K e⟩⟩

theorem projectiveOuter_secondDerived_eq_bot_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* ProjectiveQuotient K) :
    derivedSeries (Outer G) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (equivalence e).symm.toMonoidHom
    (equivalence e).symm.surjective (projectiveOuter_secondDerived_eq_bot K)

theorem projectiveOuter_solvable_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* ProjectiveQuotient K) :
    Group.IsSolvable (Outer G) :=
  ⟨⟨2, projectiveOuter_secondDerived_eq_bot_of_equiv K e⟩⟩

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
