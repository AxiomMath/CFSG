module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Stable
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Fix2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem kleinV_le_of_inf_le [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    {L : Subgroup G} (hL : IsComponent L) (hle : L ⊓ centralizer ({t} : Set G) ≤ kleinV t v) :
    kleinV t v ≤ L := by
  haveI : IsSimpleGroup ↥L := component_isSimple hF hL
  have hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := component_nonab hF hL
  obtain ⟨x, hxL, hx1, hxt⟩ :=
    exists_fixed_of_simple_nonab (L := L) (component_isSimple hF hL) hnab cfg.t_sq
      (fun y hy => conj_mem_of_component cfg hF hL hy)
  have hxC : x ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxt
  have hxV : x ∈ kleinV t v := hle ⟨hxL, hxC⟩
  have hx_sq : x * x = 1 := cfg.sq_eq_one_of_mem hxV
  have hxcent : centralizer ({x} : Set G) = centralizer ({t} : Set G) :=
    cfg.centralizer_eq_of_mem hxV hx1
  have hperf : Group.IsPerfect ↥L := isPerfect_of_simple_of_nonab (component_isSimple hF hL) hnab
  obtain ⟨y, hyL, hyx, hyx'⟩ :=
    exists_commute_not_mem_zpowers (X := L) hperf hxL hx_sq hx1
  have hycent : y ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hyx
  rw [hxcent] at hycent
  have hyV : y ∈ kleinV t v := hle ⟨hyL, hycent⟩
  have hy1 : y ≠ 1 := fun h => hyx' (h.symm ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have hyx_ne : y ≠ x := fun h => hyx' (h.symm ▸ Subgroup.mem_zpowers x)
  have hgen : zpowers x ⊔ zpowers y = kleinV t v :=
    cfg.eq_kleinV_of_ne hxV hyV hx1 hy1 (Ne.symm hyx_ne)
  rw [← hgen]
  exact sup_le (Subgroup.zpowers_le.2 hxL) (Subgroup.zpowers_le.2 hyL)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
