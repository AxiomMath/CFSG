module

public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface

public section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.QuasithinUnique.B1

theorem catalog_of_sporadicRep {S : Type} [Group S] (s : SporadicName)
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) : CFSG.Blueprint.Catalog S :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ⟨e⟩⟩)))

theorem catalogBridgeFor_sporadic_of_mulEquiv (s : SporadicName)
    (h : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* s.Group)) :
    CatalogBridgeFor (.sporadic s) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_sporadicRep s (e.trans h.some.symm)

theorem catalogBridgeFor_sporadic_of_forall
    (h : ∀ s : SporadicName, Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* s.Group))
    (s : SporadicName) : CatalogBridgeFor (.sporadic s) :=
  catalogBridgeFor_sporadic_of_mulEquiv s (h s)

end CFSG.TauCetiBridge
