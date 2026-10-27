module

public import CFSG.GH74.QTGen4.DCopy.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutRu

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def J4AutInner_F4 : Prop :=
  ∀ (K : Type) [Group K] [CFSG.GH74.QTGen4.Finite4 K], Nonempty (K ≃* NativeSporadic.Carrier .J4) → ∀ β : K ≃* K,
    (∀ x, β (β x) = x) → (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

theorem sporadicRestAutInner_of_J4_F4
    (hJ4 : J4AutInner_F4) : SporadicRestAutInner_F4 := by
  intro s hs K _ _ hK β hβ hP
  rcases hs with rfl | rfl | rfl | rfl
  · exact hJ4 K hK β hβ hP
  · exact hsAutInner K hK β hP
  · exact heAutInner K hK β hβ hP
  · exact ruAutInner K hK β hP

theorem sporadicResidualAutInner_of_J4_F4
    (hJ4 : J4AutInner_F4) : SporadicResidualAutInner_F4 :=
  sporadicResidualAutInner_of_rest_F4 (sporadicRestAutInner_of_J4_F4 hJ4)

end CFSG.QuasithinUnique.Ch1
