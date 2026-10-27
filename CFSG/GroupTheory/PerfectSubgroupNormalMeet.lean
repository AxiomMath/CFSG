module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace Subgroup

variable {Y : Type*} [Group Y]

theorem le_or_subgroupOf_le_center_of_perfect {H N : Subgroup Y} [N.Normal] (hperf : ⁅H, H⁆ = H)
    (hs : IsSimpleGroup (↥H ⧸ center ↥H)) :
    H ≤ N ∨ N.subgroupOf H ≤ center ↥H := by
  let M : Subgroup ↥H := N.subgroupOf H
  haveI hM : M.Normal := Subgroup.normal_subgroupOf
  let π : ↥H →* ↥H ⧸ center ↥H := QuotientGroup.mk' (center ↥H)
  have hker : π.ker = center ↥H := QuotientGroup.ker_mk' (center ↥H)
  haveI hmap_normal : (M.map π).Normal :=
    hM.map π (QuotientGroup.mk'_surjective (center ↥H))
  rcases hs.eq_bot_or_eq_top_of_normal (M.map π) with hbot | htop
  · right
    have h : M ≤ π.ker := (Subgroup.map_eq_bot_iff M).mp hbot
    rwa [hker] at h
  · left
    have hsup : M ⊔ center ↥H = ⊤ := by
      have h := congrArg (Subgroup.comap π) htop
      rw [Subgroup.comap_map_eq π M, hker, Subgroup.comap_top π] at h
      exact h
    have hcomm : _root_.commutator ↥H ≤ M := by
      have heq : _root_.commutator ↥H = ⁅M ⊔ center ↥H, (⊤ : Subgroup ↥H)⁆ := by
        rw [_root_.commutator_def,
          show (⊤ : Subgroup ↥H) = M ⊔ center ↥H from hsup.symm]
      rw [heq, Subgroup.commutator_sup_right]
      refine sup_le (Subgroup.commutator_le_left M (⊤ : Subgroup ↥H)) ?_
      have hz : ⁅center ↥H, (⊤ : Subgroup ↥H)⁆ = ⊥ :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr le_rfl
      exact hz.le.trans bot_le
    have hmap : ⁅H, H⁆ ≤ N :=
      calc ⁅H, H⁆ = (_root_.commutator ↥H).map H.subtype :=
            (Subgroup.map_subtype_commutator H).symm
        _ ≤ (N.subgroupOf H).map H.subtype := Subgroup.map_mono (f := H.subtype) hcomm
        _ = N ⊓ H := Subgroup.subgroupOf_map_subtype N H
        _ ≤ N := inf_le_left
    rw [← hperf]
    exact hmap

theorem index_center_dvd_index_of_perfect {H N : Subgroup Y} [N.Normal] (hperf : ⁅H, H⁆ = H)
    (hs : IsSimpleGroup (↥H ⧸ center ↥H)) (hHN : ¬ H ≤ N) :
    (center ↥H).index ∣ N.index := by
  have hle : N.subgroupOf H ≤ center ↥H :=
    (le_or_subgroupOf_le_center_of_perfect hperf hs).resolve_left hHN
  have h1 : (center ↥H).index ∣ (N.subgroupOf H).index := Subgroup.index_dvd_of_le hle
  exact h1.trans (Subgroup.relIndex_dvd_index_of_normal N H)

end Subgroup
