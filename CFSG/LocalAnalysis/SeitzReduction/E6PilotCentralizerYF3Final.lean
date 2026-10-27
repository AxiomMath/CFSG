module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Main
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYParabolic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYStab

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)


variable {K : Type} [Field K]

theorem centralizer_yD_le_of_leviStabilizerAS [CharP K 2] (hU3 : LeviStabilizerAS K) :
    centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K)) ≤
      yRadical K ⊔ yLevi K ⊔ yTorus K := by
  set n := (e6RepConj K 1 : ModGL .E6 K)
  set φ := (MulAut.conj n).toMonoidHom
  have hy := conj_e6RepConj_e6ASRep_one (K := K)
  have hmap : (parabolicLevi .E6 K nodes16 ⊓
      centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))).map φ ≤
      yLeviGL K ⊔ (torusGroup .E6 K ⊓
        centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))) := by
    refine (map_mono fun m hm => hU3 m (mem_inf.1 hm).1 (mem_inf.1 hm).2).trans ?_
    rw [Subgroup.map_sup, ← yLeviGL_eq_map_yLeviF4]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨hhT, hhC⟩ := mem_inf.1 hh
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (coe_e6RepConj_mem_normalizer_torusGroup 1) h).1 hhT,
      ?_⟩
    rw [mem_centralizer_singleton_iff] at hhC ⊢
    rw [← hy]
    change MulAut.conj n h * MulAut.conj n _ = MulAut.conj n _ * MulAut.conj n h
    rw [← map_mul, ← map_mul, hhC]
  have hle : centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ⊓ adjointGroup .E6 K ≤
      rootSpan .E6 K yRadicalRoots ⊔ yLeviGL K ⊔ (torusGroup .E6 K ⊓
        centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K))) := by
    refine centralizer_e6Rep_one_le.trans ?_
    rw [sup_assoc]
    exact sup_le_sup_left hmap _
  have hTC : torusGroup .E6 K ⊓ centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) ≤
      adjointGroup .E6 K :=
    inf_le_left.trans ((torusGroup_le_parabolicLevi nodes16).trans
      (parabolicLevi_le_adjointGroup (τ := .E6) (K := K) nodes16))
  have hQC : rootSpan .E6 K yRadicalRoots ≤ adjointGroup .E6 K := rootSpan_le_adjointGroup K _
  have hsup : yRadical K ⊔ yLevi K ⊔ yTorus K = (rootSpan .E6 K yRadicalRoots ⊔ yLeviGL K ⊔
      (torusGroup .E6 K ⊓
        centralizer ({(e6Rep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)))).subgroupOf
      (adjointGroup .E6 K) := by
    rw [subgroupOf_sup (sup_le hQC yLeviGL_le_adjointGroup) hTC,
      subgroupOf_sup hQC yLeviGL_le_adjointGroup]
    rfl
  intro g hg
  rw [hsup]
  exact mem_subgroupOf.2 (hle (mem_inf.2 ⟨(mem_centralizer_e6Rep_iff 1).1 hg, g.2⟩))

theorem factF3y_of_leviStabilizerAS [Finite K] [CharP K 2] (hU3 : LeviStabilizerAS K) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
        yRadical K ⊔ yLevi K ∧
      IsPGroup 2 (yRadical K) ∧
      yLevi K ≤ normalizer (yRadical K : Set (adjointGroup .E6 K)) ∧
      Disjoint (yRadical K) (yLevi K) ∧
      (∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ yLevi K :=
  ⟨perfectCore_centralizer_yD_eq_of_le (centralizer_yD_le_of_leviStabilizerAS hU3),
    isPGroup_yRadical, yLevi_le_normalizer_yRadical, disjoint_yRadical_yLevi,
    eq_bot_of_normal_isPGroup_yLevi, highRootSL2_le_yLevi⟩

end CFSG.SeitzReduction.E6Pilot
