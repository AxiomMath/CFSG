module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_sup_eq_relIndex_inf_of_le_normalizer {H K : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K ∧
      K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    let NG : Subgroup G := Subgroup.normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := Subgroup.le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    let : (K.subgroupOf NG).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKleNG).2 le_rfl
    calc
      K.relIndex (H ⊔ K) = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) := by
        exact (Subgroup.relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
        rw [Subgroup.subgroupOf_sup (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
        calc
          (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG))
              = (K.subgroupOf NG).relIndex (H.subgroupOf NG) := by
                exact Subgroup.relIndex_sup_right (H := H.subgroupOf NG) (K := K.subgroupOf NG)
          _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
                exact (Subgroup.inf_relIndex_left (H := H.subgroupOf NG)
                  (K := K.subgroupOf NG)).symm
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
        rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
          ext x
          simp [Subgroup.mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := by
        exact Subgroup.relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hHleNG
  refine ⟨?_, hKrel⟩
  have hmul : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) :=
        Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K) inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) := by
        symm
        exact Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K) inf_le_right
          le_sup_right
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := by
    have hne : (H ⊓ K).relIndex H ≠ 0 := by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H)
    exact Nat.pos_of_ne_zero hne
  have hmul' : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex H * (H ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

end CFSG.GroupTheory
