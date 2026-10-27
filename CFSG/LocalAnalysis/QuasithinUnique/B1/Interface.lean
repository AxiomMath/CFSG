module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Interfaces

public section

namespace CFSG.QuasithinUnique.B1

open CFSG.Assembly

@[expose] def CatalogBridgeFor (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], Nonempty (S ≃* i.Group) →
    CFSG.Blueprint.Catalog S

theorem catalog_of_comm (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : CFSG.Blueprint.Catalog S :=
  CFSG.SectionRank.catalog_containsAbelianSimple S hcomm

theorem catalogBridgeFor_cyclic (p : ℕ) (hp : p.Prime) :
    CatalogBridgeFor (.cyclic p hp) := by
  intro S _ _ _ ⟨e⟩
  exact Or.inl ⟨p, hp, ⟨e⟩⟩

theorem catalogBridgeFor_alternating (n : ℕ) (hn : 5 ≤ n) :
    CatalogBridgeFor (.alternating n hn) := by
  intro S _ _ _ ⟨e⟩
  exact Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩)

theorem catalog_of_inCatalog (h : ∀ i, CatalogBridgeFor i) (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (hS : InCatalog S) : CFSG.Blueprint.Catalog S := by
  obtain ⟨i, hi⟩ := hS
  exact h i S hi

theorem tcKGroupBridge_of_bridges (h : ∀ i, CatalogBridgeFor i) : TCKGroupBridge :=
  fun _ _ _ hK => kGroupAllSimple_of_kGroupNonab_of_catalogImp
    (fun S _ _ _ _ hS => catalog_of_inCatalog h S hS) CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hK

end CFSG.QuasithinUnique.B1
