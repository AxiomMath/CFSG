module

public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogFourth

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.R2

open Subgroup CFSG.Blueprint

theorem card_centralizer_of_isConj {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc, card_centralizer_conj]

theorem card_centralizer_subgroup {G : Type*} [Group G] (H : Subgroup G) (h : H) :
    Nat.card (centralizer ({h} : Set H)) = Nat.card ↥(H ⊓ centralizer ({(h : G)} : Set G)) := by
  have hmap : (centralizer ({h} : Set H)).map H.subtype = H ⊓ centralizer ({(h : G)} : Set G) := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxc⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxc), rfl⟩
  rw [← hmap, card_map_of_injective H.subtype_injective]

end CFSG.LocalAnalysis.EvenBN.Tits.R2
