module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type} [Group G] [Finite G]

theorem EscapingQuotientData.caseOneConfig {H : Subgroup G} {x : G}
    (hq : EscapingQuotientData H x) {J : Subgroup (EscapingQuotient x)}
    (hJ : CFSG.IsComponent J) (hxJ : escapingBar x ∉ J) : CaseOneConfig x J where
  bar_not_mem := hxJ
  involution_mem := fun _ ht => hq.involution_mem_component_or hJ hxJ ht
  conj := fun _ ha _ hb ha2 hb2 => by
    obtain ⟨c, -, hc⟩ := hq.component_conj hJ hxJ ha hb ha2 hb2
    exact isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hc⟩
  four := exists_commuting_involutions_of_two_le_pRank (hq.component_two_le_pRank hJ hxJ)

theorem not_isConj_of_centralizer_le {S : Sylow 2 G} {H : Subgroup G} {z u : G}
    (hset : CoreSetting G S H) (hzH : z ∈ H) (hz : orderOf z = 2)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ H) (huH : u ∈ H)
    (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) : ¬ IsConj z u := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨k, hk, hkz⟩ := two_generated_core_controls_involution_fusion S H hset.sylow_le
    hset.core_le z hzH hz g⁻¹ (by rw [inv_inv, hg]; exact huH)
  exact hesc (centralizer_le_of_conj hk (hkz.trans (by rw [inv_inv, hg])) hzC)

section CaseOne

variable {S : Sylow 2 G} {H : Subgroup G} {z u : G} (hset : CoreSetting G S H) (hzH : z ∈ H)
  (hz : orderOf z = 2) (hzC : Subgroup.centralizer ({z} : Set G) ≤ H) (hu : orderOf u = 2)
  (huz : Commute u z) (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
  {J : Subgroup (EscapingQuotient u)} (hJ : CFSG.IsComponent J) (huJ : escapingBar u ∉ J)
include hset hzH hz hzC hu huz hesc hJ huJ

theorem not_mem_localInvolutionPointHull_of_caseOne_of_commute :
    u ∉ localInvolutionPointHull z u := by
  have huH : u ∈ H := hzC (Subgroup.mem_centralizer_singleton_iff.mpr huz.eq)
  exact ((escapingQuotientData hset huH hu hesc).caseOneConfig hJ huJ
    ).not_mem_localInvolutionPointHull hset.simple hset.nonabelian hu
    (w := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr huz.eq.symm⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz)
    (not_isConj_of_centralizer_le hset hzH hz hzC huH hesc)

end CaseOne

theorem not_mem_localInvolutionPointHull_of_caseOne (S : Sylow 2 G) (H : Subgroup G) (z : G)
    (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hzC : Subgroup.centralizer ({z} : Set G) ≤ H)
    (u : G) (hu : orderOf u = 2) (huS : u ∈ (S : Subgroup G))
    (_hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
        Subgroup G))
    (_hrank : 3 ≤ CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G)))
    (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hcase : ∃ J : Subgroup (EscapingQuotient u), CFSG.IsComponent J ∧ escapingBar u ∉ J) :
    u ∉ localInvolutionPointHull z u := by
  obtain ⟨J, hJ, huJ⟩ := hcase
  exact not_mem_localInvolutionPointHull_of_caseOne_of_commute hset (hset.sylow_le hz.1) hz.2.1
    hzC hu (hz.2.2 u huS) hesc hJ huJ

@[expose] def HighRankEscapingStepCaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    CoreSetting G S H → IsCentralInvolution (S : Subgroup G) z →
      Subgroup.centralizer ({z} : Set G) ≤ H →
      ∀ u : G, orderOf u = 2 → u ∈ (S : Subgroup G) →
        (∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
          Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) :
            Subgroup G)) →
        3 ≤ CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G)) →
        ¬ Subgroup.centralizer ({u} : Set G) ≤ H →
        (∀ J : Subgroup (EscapingQuotient u), CFSG.IsComponent J → escapingBar u ∈ J) →
        u ∉ localInvolutionPointHull z u

theorem highRankEscapingStep_of_caseTwo (h : HighRankEscapingStepCaseTwo) :
    HighRankEscapingStep := by
  intro G _ _ S H z hset hz hzC u hu huS hsyl hrank hesc
  by_cases hcase : ∃ J : Subgroup (EscapingQuotient u), CFSG.IsComponent J ∧ escapingBar u ∉ J
  · exact not_mem_localInvolutionPointHull_of_caseOne S H z hset hz hzC u hu huS hsyl hrank hesc
      hcase
  · push Not at hcase
    exact h G S H z hset hz hzC u hu huS hsyl hrank hesc hcase

end CFSG.ProperTwoGeneratedCore.Assembly
