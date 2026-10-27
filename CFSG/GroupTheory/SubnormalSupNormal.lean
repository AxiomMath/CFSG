module

public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.GroupTheory

open Subgroup

variable {Y : Type*} [Group Y]

theorem isSubnormal_of_sup_eq_top {B H N : Subgroup Y} (hBH : B ≤ H)
    (hB : (B.subgroupOf H).IsSubnormal) (hN : N.Normal) (hNB : N ≤ normalizer (B : Set Y))
    (hNH : N ⊔ H = ⊤) : B.IsSubnormal := by
  have : N.Normal := hN
  have hmap : H.map (QuotientGroup.mk' N) = ⊤ := by
    have h1 : (N ⊔ H).map (QuotientGroup.mk' N) = H.map (QuotientGroup.mk' N) := by
      rw [Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff N).mpr (le_of_eq (QuotientGroup.ker_mk' (N := N)).symm),
        bot_sup_eq]
    rw [hNH, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  have hsub : (B ⊔ N).IsSubnormal := by
    have h := (hB.map hsurj).comap (QuotientGroup.mk' N)
    rwa [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hBH,
      Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have hnormal : (B.subgroupOf (B ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hNB)
  exact IsSubnormal.trans le_sup_left hnormal.isSubnormal hsub

end CFSG.GroupTheory
