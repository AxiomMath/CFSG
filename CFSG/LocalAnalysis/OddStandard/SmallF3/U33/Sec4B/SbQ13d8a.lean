module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem ncard_mul_set_mul_card_inf (H K : Subgroup G) :
    ((H : Set G) * (K : Set G)).ncard * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (H : Set G)
  have himg : Nat.card ↥((H : Set G).image ((↑) : G → G ⧸ K)) = K.relIndex H := by
    have horb : MulAction.orbit ↥H ((1 : G) : G ⧸ K) = (H : Set G).image ((↑) : G → G ⧸ K) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥H ((1 : G) : G ⧸ K) = K.subgroupOf H := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ K)) = ((a : G) : G ⧸ K) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using K.inv_mem h
      · intro h
        simpa using K.inv_mem h
    have := MulAction.index_stabilizer ↥H ((1 : G) : G ⧸ K)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card K H
  rw [inf_comm K H] at h2
  rw [← Nat.card_coe_set_eq, h1, himg]
  calc Nat.card ↥K * K.relIndex H * Nat.card ↥(H ⊓ K)
      = Nat.card ↥K * (K.relIndex H * Nat.card ↥(H ⊓ K)) := Nat.mul_assoc _ _ _
    _ = Nat.card ↥H * Nat.card ↥K := by rw [h2, Nat.mul_comm]

theorem q13d_card_mul_le_card_sup_mul_card_inf (H K : Subgroup G) :
    Nat.card ↥H * Nat.card ↥K ≤ Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) := by
  have hsub : ((H : Set G) * (K : Set G)) ⊆ ((H ⊔ K : Subgroup G) : Set G) := by
    rintro x ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk
  have hle : ((H : Set G) * (K : Set G)).ncard ≤ Nat.card ↥(H ⊔ K) := by
    rw [show Nat.card ↥(H ⊔ K) = ((H ⊔ K : Subgroup G) : Set G).ncard from rfl]
    exact Set.ncard_le_ncard hsub
  calc Nat.card ↥H * Nat.card ↥K
      = ((H : Set G) * (K : Set G)).ncard * Nat.card ↥(H ⊓ K) :=
        (ncard_mul_set_mul_card_inf H K).symm
    _ ≤ Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) := Nat.mul_le_mul_right _ hle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
