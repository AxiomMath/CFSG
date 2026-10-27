module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem secProp_cyclic_of_sup_zpowers {P1 P0 : Subgroup G} {t : G} (hle : P0 ≤ P1)
    (hnorm : P1 ≤ normalizer (P0 : Set G)) (hsplit : P1 = P0 ⊔ zpowers t) :
    SecProp P1 P0 (fun Y _ _ _ => IsCyclic Y) := by
  have hn : (P0.subgroupOf P1).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
  refine ⟨hn, ?_⟩
  have htP : t ∈ P1 := hsplit ▸ (le_sup_right : zpowers t ≤ P0 ⊔ zpowers t) (mem_zpowers t)
  have hZ : zpowers t ≤ P1 := (zpowers_le).mpr htP
  have htop : P0.subgroupOf P1 ⊔ (zpowers t).subgroupOf P1 = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hle hZ, ← hsplit, Subgroup.subgroupOf_self]
  refine ⟨QuotientGroup.mk ⟨t, htP⟩, fun q => ?_⟩
  obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
  have hq : q' ∈ P0.subgroupOf P1 ⊔ (zpowers t).subgroupOf P1 := htop ▸ Subgroup.mem_top q'
  have hW : P0.subgroupOf P1 ⊔ (zpowers t).subgroupOf P1 ≤
      (zpowers (QuotientGroup.mk (⟨t, htP⟩ : ↥P1) : ↥P1 ⧸ P0.subgroupOf P1)).comap
        (QuotientGroup.mk' (P0.subgroupOf P1)) := by
    refine sup_le (fun n hn => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact one_mem _
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
      have hz' : z = (⟨t, htP⟩ : ↥P1) ^ k := Subtype.ext (by simpa using hk.symm)
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, hz', QuotientGroup.mk_zpow]
      exact zpow_mem_zpowers _ _
  exact hW hq

end CFSG.OddStandard.HigherRank.YamadaG23
