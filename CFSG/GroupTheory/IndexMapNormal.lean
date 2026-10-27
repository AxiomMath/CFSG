module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GroupTheory

theorem index_eq_relIndex_mul_index_map {H : Type*} [Group H] [Finite H] (N C : Subgroup H)
    [N.Normal] :
    C.index = (N ⊓ C).relIndex N * (C.map (QuotientGroup.mk' N)).index := by
  let f : C →* H ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hker : f.ker = N.subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq_one_iff (x : H))
  have hrange : f.range = C.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv] at h1
  have h2 := Subgroup.card_mul_index C
  have h3 := Subgroup.card_mul_index (C.map (QuotientGroup.mk' N))
  have h4 := Subgroup.relIndex_mul_card (N ⊓ C) N
  rw [inf_eq_left.mpr (inf_le_left : N ⊓ C ≤ N)] at h4
  have h5 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hC : 0 < Nat.card C := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hC
  calc Nat.card C * C.index = Nat.card H := h2
    _ = Nat.card (H ⧸ N) * Nat.card N := h5
    _ = ((C.map (QuotientGroup.mk' N)).index * Nat.card (C.map (QuotientGroup.mk' N))) *
          ((N ⊓ C).relIndex N * Nat.card ↥(N ⊓ C)) := by
        rw [h4, mul_comm (Subgroup.index _), h3]
    _ = Nat.card C * ((N ⊓ C).relIndex N * (C.map (QuotientGroup.mk' N)).index) := by
        rw [← h1]
        ring

end CFSG.GroupTheory
