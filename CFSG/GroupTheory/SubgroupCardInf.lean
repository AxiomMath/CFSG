module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG

theorem card_mul_card_le_card_inf_mul_card_of_le {G : Type*} [Group G] [Finite G]
    {H K C : Subgroup G} (hH : H ≤ C) (hK : K ≤ C) :
    Nat.card H * Nat.card K ≤ Nat.card ↥(H ⊓ K) * Nat.card C := by
  have e1 : K.relIndex H * Nat.card ↥(H ⊓ K) = Nat.card H := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H)
    rwa [inf_comm] at h
  have e2 : K.relIndex (H ⊔ K) * Nat.card K = Nat.card ↥(H ⊔ K) := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := H ⊔ K)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hne : K.relIndex (H ⊔ K) ≠ 0 := by
    intro h
    rw [h, zero_mul] at e2
    exact (Nat.card_pos (α := ↥(H ⊔ K))).ne' e2.symm
  have hle : K.relIndex H ≤ K.relIndex (H ⊔ K) :=
    Subgroup.relIndex_le_of_le_right (H := K) (K := H) (L := H ⊔ K) le_sup_left hne
  calc Nat.card H * Nat.card K
      = K.relIndex H * Nat.card ↥(H ⊓ K) * Nat.card K := by rw [← e1]
    _ ≤ K.relIndex (H ⊔ K) * Nat.card ↥(H ⊓ K) * Nat.card K := by gcongr
    _ = Nat.card ↥(H ⊓ K) * Nat.card ↥(H ⊔ K) := by
      rw [← e2, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ Nat.card ↥(H ⊓ K) * Nat.card C :=
      Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (sup_le hH hK))

end CFSG
