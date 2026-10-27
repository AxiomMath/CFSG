module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.GH74.QTGen4.DCopy.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.J2Cover

@[expose] def SporadicRestAutInner_F4 : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSporadicRestName s → ∀ (K : Type) [Group K] [CFSG.GH74.QTGen4.Finite4 K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

theorem sporadicResidualAutInner_of_rest_F4
    (h : SporadicRestAutInner_F4) :
    SporadicResidualAutInner_F4 := by
  intro s hs K _ _ hK β hβ hP
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact j2AutInner K hK β hβ hP
  · exact h .J4 (Or.inl rfl) K hK β hβ hP
  · exact h .HS (Or.inr (Or.inl rfl)) K hK β hβ hP
  · exact h .He (Or.inr (Or.inr (Or.inl rfl))) K hK β hβ hP
  · exact h .Ru (Or.inr (Or.inr (Or.inr rfl))) K hK β hβ hP

end CFSG.QuasithinUnique.Ch1
