module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Facts

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mem_derivedCentralizer {u g h : G}
    (hg : g ∈ centralizer ({u} : Set G)) (hh : h ∈ centralizer ({u} : Set G)) :
    ⁅g, h⁆ ∈ derivedCentralizer u := by
  refine ⟨⁅(⟨g, hg⟩ : centralizer ({u} : Set G)), ⟨h, hh⟩⁆, ?_, rfl⟩
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem map_centralizer_subtype_eq (K : Subgroup G) (t : K) :
    (centralizer ({t} : Set K)).map K.subtype = K ⊓ centralizer ({(t : G)} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, congrArg Subtype.val hy⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hc, rfl⟩

theorem card_centralizer_subtype (K : Subgroup G) (t : K) :
    Nat.card (centralizer ({t} : Set K)) =
      Nat.card (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  rw [← map_centralizer_subtype_eq, Subgroup.card_subtype]

theorem card_centralizer_inf_subtype (K : Subgroup G) (t s : K) :
    Nat.card ↥(centralizer ({t} : Set K) ⊓ centralizer ({s} : Set K)) =
      Nat.card (K ⊓ centralizer ({(t : G)} : Set G) ⊓ centralizer ({(s : G)} : Set G) :
        Subgroup G) := by
  have h : (centralizer ({t} : Set K) ⊓ centralizer ({s} : Set K)).map K.subtype =
      K ⊓ centralizer ({(t : G)} : Set G) ⊓ centralizer ({(s : G)} : Set G) := by
    rw [Subgroup.map_inf _ _ _ K.subtype_injective, map_centralizer_subtype_eq,
      map_centralizer_subtype_eq]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [← h, Subgroup.card_subtype]

end CFSG.EvenSporadicStandard.RuStd
