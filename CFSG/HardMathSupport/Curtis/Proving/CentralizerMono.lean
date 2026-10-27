module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Subgroup

theorem card_centralizer_subtype_dvd {G : Type*} [Group G] [Finite G] {A : Subgroup G} {s : G}
    (hs : s ∈ A) :
    Nat.card (centralizer ({(⟨s, hs⟩ : A)} : Set A)) ∣ Nat.card (centralizer ({s} : Set G)) := by
  set C := centralizer ({(⟨s, hs⟩ : A)} : Set A) with hC
  have hle : C.map A.subtype ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ centralizer ({(⟨s, hs⟩ : A)} : Set A) := hx
    rw [mem_centralizer_singleton_iff] at hx' ⊢
    simpa using congrArg Subtype.val hx'
  rw [← Subgroup.card_map_of_injective A.subtype_injective]
  exact Subgroup.card_dvd_of_le hle

theorem eightyOne_dvd_centralizer_of_sub {G : Type*} [Group G] [Finite G] {A : Subgroup G} {s : G}
    (hs : s ∈ A)
    (h : 81 ∣ Nat.card (centralizer ({(⟨s, hs⟩ : A)} : Set A))) :
    81 ∣ Nat.card (centralizer ({s} : Set G)) :=
  h.trans (card_centralizer_subtype_dvd hs)

end CFSG.HardMathSupport.Curtis.Proving

end
