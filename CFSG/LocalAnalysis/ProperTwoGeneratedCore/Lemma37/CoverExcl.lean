module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoverExclCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleSplit
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
public import CFSG.Walter.J1Props.Multiplier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderCoverStatement

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

namespace CoverExcl

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

theorem center_isPGroup (hq : EscapingQuotientData H z) (hJ : CFSG.IsComponent J) :
    IsPGroup 2 (Subgroup.center J) :=
  (component_center_le_twoCore hq.oddCore_eq_bot hJ).1

theorem eq_bar_of_mem_center (hq : EscapingQuotientData H z) (hJ : CFSG.IsComponent J) {c : J}
    (hc : c ∈ Subgroup.center J) (h2 : orderOf c = 2) :
    (c : EscapingQuotient z) = escapingBar z :=
  eq_of_mem_twoCore_of_rank_one hq.bar_mem_center hq.bar_order hq.bar_mem_twoCore
    hq.twoCore_rank ((component_center_le_twoCore hq.oddCore_eq_bot hJ).2
      (Subgroup.mem_map_of_mem _ hc)) (by rwa [Subgroup.orderOf_coe])

theorem center_isCyclic (hq : EscapingQuotientData H z) (hJ : CFSG.IsComponent J) :
    IsCyclic (Subgroup.center J) := by
  refine CFSG.ABGLocalTools.isCyclic_of_isPGroup_two_of_comm (center_isPGroup hq hJ)
    (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)) fun u v hu hv =>
      Subtype.ext (Subtype.ext ?_)
  have hu' : orderOf (u : J) = 2 := by rwa [Subgroup.orderOf_coe]
  have hv' : orderOf (v : J) = 2 := by rwa [Subgroup.orderOf_coe]
  rw [eq_bar_of_mem_center hq hJ u.2 hu', eq_bar_of_mem_center hq hJ v.2 hv']

theorem bar_mem_center (hq : EscapingQuotientData H z) (hzJ : escapingBar z ∈ J) :
    (⟨escapingBar z, hzJ⟩ : J) ∈ Subgroup.center J :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp
    hq.bar_mem_center g)

theorem center_ne_bot (hq : EscapingQuotientData H z) (hzJ : escapingBar z ∈ J) :
    Subgroup.center J ≠ ⊥ := by
  intro hbot
  have h := bar_mem_center hq hzJ
  rw [hbot, Subgroup.mem_bot] at h
  have h2 := hq.bar_order
  rw [show escapingBar z = 1 from congrArg Subtype.val h, orderOf_one] at h2
  exact absurd h2 (by decide)

end CoverExcl

theorem center_eq_bot_of_quotient_jOne {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (e : (K ⧸ Subgroup.center K) ≃* properTwoGenCoreJ1) :
    Subgroup.center K = ⊥ := by
  let e' := e.trans (MulEquiv.subgroupCongr CFSG.Walter.walterJ1_eq_properTwoGenCoreJ1.symm)
  let π := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp [π]
  rw [← hker]
  exact CFSG.Walter.J1Props.J3_multiplier π
    (e'.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le hperf

theorem squareCaseCoverExcluded_of (hrank2 : RankTwoCoverStatement)
    (hsz : SquareCaseSzEightExcluded) : SquareCaseCoverExcluded := by
  intro G _ _ S H z hS J hJ hJH hrank hK hBJ
  have hq : EscapingQuotientData H z := escapingQuotientData hS.core
    (hS.core.sylow_le hS.central.1) hS.central.2.1 hS.escape
  have hzJ : escapingBar z ∈ J := hS.caseTwo J hJ
  have h2 := CoverExcl.center_isPGroup hq hJ
  have hcyc := CoverExcl.center_isCyclic hq hJ
  have hne := CoverExcl.center_ne_bot hq hzJ
  obtain ⟨hperf, hsimple, hnonab⟩ := hJ.1
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hsimple
  rcases hBJ with hB | hJ1
  · rcases CoverExcl.bender_cover_quotient_of_isCyclic hperf.commutator_eq_top h2 hcyc hne
      hnonab hB with h | h
    ·
      obtain ⟨e⟩ := h
      have hr : CFSG.Open.twoRank (J ⧸ Subgroup.center J) = 2 :=
        CFSG.GH74.twoRank_eq_of_mulEquiv_psl2Model (by norm_num) e
      obtain ⟨x, hxJ, hx2, hxz⟩ := hrank
      have heq := hrank2 J hperf.commutator_eq_top h2 hne hcyc hsimple hr ⟨x, hxJ⟩
        ⟨escapingBar z, hzJ⟩ (by rwa [Subgroup.orderOf_mk])
        (by rw [Subgroup.orderOf_mk]; exact hq.bar_order)
      exact hxz (congrArg Subtype.val heq)
    · exact hsz G S H z hS J hJ hJH hrank hK h
  · obtain ⟨e⟩ := hJ1
    exact hne (center_eq_bot_of_quotient_jOne hperf.commutator_eq_top e)

end CFSG.ProperTwoGeneratedCore.Lemma37
