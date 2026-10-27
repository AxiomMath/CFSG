module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G2K
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84v_gamma_mem_normalizer (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} {γ : G} {K U : Subgroup G}
    (h : Sec8Gamma G t L S z g B γ K U) : γ ∈ normalizer (L : Set G) :=
  sec4_mem_normalizer F.h36 h.ctx.toSec3SettingLB γ (h.ctx.sylow.1 h.mem)

theorem sec8t84v_t_mem_normalizer {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} {γ : G} {K U : Subgroup G}
    (h : Sec8Gamma G t L S z g B γ K U) : t ∈ normalizer (K : Set G) := by
  have hγt : γ ∈ centralizer ({t} : Set G) := h.ctx.sylow.1 h.mem
  have htγ : t ∈ centralizer ({γ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hγt ⊢
    exact hγt.symm
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer h.comp.1).mp h.normal) htγ

theorem sec8t84v_K0_comp_inf (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} {γ : G} {K U : Subgroup G}
    (h : Sec8Gamma G t L S z g B γ K U) :
    IsComponentIn (layerCent L γ) (K ⊓ centralizer ({t} : Set G)) := by
  obtain ⟨-, -, -, hcomp, -⟩ := sec8t84g_K0_comp F h.ctx h.mem h.inv h.outer
  exact hcomp.mono (le_inf h.layer_le (hcomp.le.trans inf_le_right))
    (inf_le_inf_right _ h.comp.le)

end CFSG.OddStandard.SmallF3.Omega
