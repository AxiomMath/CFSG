module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNSporOrd
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNSporB
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNSporM

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

@[expose] def HNSporadicClause : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ x y : S, x * y ≠ y * x) →
    NativeSporadic.SporadicRep S → ∀ (σ : MulAut S) (P : Subgroup S),
    ProperFixedComponent σ P → ¬ IsHNType (↥P ⧸ Open.fusionZStar ↥P)

theorem hnSporadicClause_holds :
    HNSporadicClause := by
  intro S _ _ _ hna hsp σ P h
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hB : s = .B
  · subst hB
    exact not_isHNType_of_properFixedComponent_B hna e h
  by_cases hM : s = .M
  · subst hM
    exact not_isHNType_of_properFixedComponent_M hna e h
  exact not_isHNType_of_properFixedComponent_sporadic_order hB hM e h

end CFSG.ComponentClassification.EvenPump
