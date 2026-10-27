module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

variable {G : Type*} [Group G]

theorem relIndex_inf_le_relIndex_of_le [Finite G] (T Q K : Subgroup G) :
    (T ⊓ Q).relIndex (T ⊓ K) ≤ Q.relIndex K := by
  have hS : (T ⊓ Q).subgroupOf (T ⊓ K) = Q.subgroupOf (T ⊓ K) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨(Subgroup.mem_inf.mp x.2).1, h⟩⟩
  rw [Subgroup.relIndex, Subgroup.relIndex, hS]
  exact Finite.card_le_of_embedding (Subgroup.quotientSubgroupOfEmbeddingOfLE Q inf_le_right)

theorem card_inf_le_relIndex_mul [Finite G] (T Q K : Subgroup G) (hQK : Q ≤ K) :
    Nat.card (T ⊓ K : Subgroup G) ≤ Q.relIndex K * Nat.card (T ⊓ Q : Subgroup G) := by
  have h1 := Subgroup.relIndex_mul_card (H := T ⊓ Q) (K := T ⊓ K)
  rw [inf_eq_left.mpr (inf_le_inf le_rfl hQK)] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (relIndex_inf_le_relIndex_of_le T Q K)

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
