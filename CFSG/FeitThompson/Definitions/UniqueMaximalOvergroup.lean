module
public import Mathlib.Order.Atoms
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

structure IsUniqueMaximalOvergroup (X M : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  le : X ≤ M
  eq_of_isCoatom : ∀ ⦃N : Subgroup G⦄, IsCoatom N → X ≤ N → N = M

namespace IsUniqueMaximalOvergroup

variable {X M M' : Subgroup G}

theorem ne_top (h : IsUniqueMaximalOvergroup X M) : X ≠ ⊤ := fun hX =>
  h.isCoatom.1 (top_le_iff.1 (hX ▸ h.le))

theorem lt_top (h : IsUniqueMaximalOvergroup X M) : X < ⊤ := lt_top_iff_ne_top.2 h.ne_top

theorem unique (h : IsUniqueMaximalOvergroup X M) (h' : IsUniqueMaximalOvergroup X M') :
    M = M' := h'.eq_of_isCoatom h.isCoatom h.le

theorem setOf_eq_singleton (h : IsUniqueMaximalOvergroup X M) :
    {N : Subgroup G | IsCoatom N ∧ X ≤ N} = {M} := by
  ext N
  exact ⟨fun hN => h.eq_of_isCoatom hN.1 hN.2, fun hN => hN ▸ ⟨h.isCoatom, h.le⟩⟩

theorem le_of_ne_top [IsCoatomic (Subgroup G)] (h : IsUniqueMaximalOvergroup X M)
    {N : Subgroup G} (hXN : X ≤ N) (hN : N ≠ ⊤) : N ≤ M := by
  obtain ⟨K, hK, hNK⟩ := (IsCoatomic.eq_top_or_exists_le_coatom N).resolve_left hN
  exact h.eq_of_isCoatom hK (hXN.trans hNK) ▸ hNK

theorem mono [IsCoatomic (Subgroup G)] (h : IsUniqueMaximalOvergroup X M) {Y : Subgroup G}
    (hXY : X ≤ Y) (hY : Y ≠ ⊤) : IsUniqueMaximalOvergroup Y M where
  isCoatom := h.isCoatom
  le := h.le_of_ne_top hXY hY
  eq_of_isCoatom _ hN hYN := h.eq_of_isCoatom hN (hXY.trans hYN)

end IsUniqueMaximalOvergroup

theorem isUniqueMaximalOvergroup_iff (X M : Subgroup G) :
    IsUniqueMaximalOvergroup X M ↔ {N : Subgroup G | IsCoatom N ∧ X ≤ N} = {M} := by
  refine ⟨IsUniqueMaximalOvergroup.setOf_eq_singleton, fun h => ?_⟩
  obtain ⟨hM, hXM⟩ : IsCoatom M ∧ X ≤ M := (Set.ext_iff.1 h M).2 rfl
  exact ⟨hM, hXM, fun N hN hXN => (Set.ext_iff.1 h N).1 ⟨hN, hXN⟩⟩

theorem exists_isUniqueMaximalOvergroup [IsCoatomic (Subgroup G)] {X : Subgroup G} (hX : X ≠ ⊤)
    (h : ∀ N N' : Subgroup G, IsCoatom N → X ≤ N → IsCoatom N' → X ≤ N' → N = N') :
    ∃ M, IsUniqueMaximalOvergroup X M := by
  obtain ⟨M, hM, hXM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom X).resolve_left hX
  exact ⟨M, hM, hXM, fun N hN hXN => h N M hN hXN hM hXM⟩

end CFSG.FeitThompson
