module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {G α : Type*} [Group G] [MulAction G α]

theorem card_orbit_mul_card_stabilizer (x : α) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card]

theorem card_le_mul_card_stabilizer {x : α} {S : Set α} (hS : S.Finite)
    (h : MulAction.orbit G x ⊆ S) :
    Nat.card G ≤ S.ncard * Nat.card (MulAction.stabilizer G x) := by
  rw [← card_orbit_mul_card_stabilizer (G := G) x, Nat.card_coe_set_eq]
  exact Nat.mul_le_mul_right _ (Set.ncard_le_ncard h hS)

theorem card_orbit_subgroup_mul_card_inf_stabilizer (H : Subgroup G) (x : α) :
    Nat.card (MulAction.orbit H x) * Nat.card ↥(H ⊓ MulAction.stabilizer G x) = Nat.card H := by
  have h := Subgroup.relIndex_mul_card (H := MulAction.stabilizer G x) (K := H)
  rw [Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer, inf_comm] at h
  rw [Nat.card_coe_set_eq]
  exact h

theorem eq_top_of_stabilizer_le_of_orbit_subset (K : Subgroup G) (x : α)
    (hK : MulAction.stabilizer G x ≤ K)
    (horb : ∀ y ∈ MulAction.orbit G x, y ∈ MulAction.orbit K x) : K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨⟨k, hk⟩, hkx⟩ := horb (g • x) (MulAction.mem_orbit x g)
  have hkx' : k • x = g • x := hkx
  have hmem : k⁻¹ * g ∈ MulAction.stabilizer G x := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hkx', inv_smul_smul]
  have := K.mul_mem hk (hK hmem)
  simpa using this

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
