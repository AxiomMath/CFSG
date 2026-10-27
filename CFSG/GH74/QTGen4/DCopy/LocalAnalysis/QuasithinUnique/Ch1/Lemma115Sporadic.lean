module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def SporadicAutInner_F4 : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSQTKSporadicName s → s ≠ .J1 → ∀ (K : Type) [Group K] [CFSG.GH74.QTGen4.Finite4 K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

end CFSG.QuasithinUnique.Ch1
