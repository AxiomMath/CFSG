module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem inSubgroup_le (F : (X : Type) → [Group X] → Subgroup X) (H : Subgroup G) :
    CFSG.inSubgroup F H ≤ H :=
  Subgroup.map_subtype_le _

theorem IsComponentIn.le_layer {J H : Subgroup G} (h : IsComponentIn J H) :
    J ≤ CFSG.inSubgroup CFSG.layer H := by
  unfold CFSG.inSubgroup
  rw [CFSG.layer.eq_sSup, ← Subgroup.map_subgroupOf_eq_of_le h.1]
  exact Subgroup.map_mono (le_sSup h.2)

theorem inSubgroup_layer_le {H N : Subgroup G}
    (h : ∀ J : Subgroup G, IsComponentIn J H → J ≤ N) :
    CFSG.inSubgroup CFSG.layer H ≤ N := by
  unfold CFSG.inSubgroup
  rw [CFSG.layer.eq_sSup]
  have hs : sSup {K : Subgroup ↥H | CFSG.IsComponent K} ≤ N.comap H.subtype := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine h (K.map H.subtype) ⟨Subgroup.map_subtype_le K, ?_⟩
    show CFSG.IsComponent ((K.map H.subtype).comap H.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective K]
    exact hK
  exact (Subgroup.map_mono hs).trans (Subgroup.map_comap_le _ _)

end CFSG.OddStandard.SmallF3.Omega
