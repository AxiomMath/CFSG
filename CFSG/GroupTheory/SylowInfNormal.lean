module

public import CFSG.GroupTheory.SteinbergCBFTHall
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG

open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem isSylowTwoOf_inf_of_normal {S X N : Subgroup G} [Finite ↥X]
    (hS : IsSylowTwoOf S X) (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (N ⊓ S) N := by
  refine ⟨inf_le_left, hS.2.1.to_le inf_le_right, ?_⟩
  have h1 : (N ⊓ S).relIndex N = S.relIndex N := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right S N
  let SX : Subgroup ↥X := S.subgroupOf X
  let NX : Subgroup ↥X := N.subgroupOf X
  have hNXn : NX.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hN
  haveI : NX.Normal := hNXn
  have hSXle : SX ≤ Subgroup.normalizer (NX : Set ↥X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hNXn]
    exact le_top
  have h2' : SX.relIndex NX = SX.relIndex (SX ⊔ NX) :=
    CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hSXle
  have h2 : S.relIndex N = S.relIndex (S ⊔ N) := by
    calc S.relIndex N = SX.relIndex NX :=
          (Subgroup.relIndex_subgroupOf (H := S) (K := N) (L := X) hNX).symm
      _ = SX.relIndex (SX ⊔ NX) := h2'
      _ = SX.relIndex ((S ⊔ N).subgroupOf X) := by
          rw [Subgroup.subgroupOf_sup hS.1 hNX]
      _ = S.relIndex (S ⊔ N) :=
          Subgroup.relIndex_subgroupOf (H := S) (K := S ⊔ N) (L := X) (sup_le hS.1 hNX)
  have h3 : S.relIndex (S ⊔ N) ∣ S.relIndex X := by
    rw [← Subgroup.relIndex_mul_relIndex S (S ⊔ N) X le_sup_left (sup_le hS.1 hNX)]
    exact dvd_mul_right _ _
  intro h
  apply hS.2.2
  change 2 ∣ S.relIndex X
  change 2 ∣ (N ⊓ S).relIndex N at h
  rw [h1, h2] at h
  exact h.trans h3
