module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup
open scoped commutatorElement

theorem isPerfect_of_simple_of_nonab' {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hm : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [_root_.commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [_root_.commutator_def]
    exact ht

theorem isPerfect_of_simple_of_nonab {K : Type*} [Group K] {S : Subgroup K}
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) :
    Group.IsPerfect ↥S := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  exact isPerfect_of_simple_of_nonab' ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
