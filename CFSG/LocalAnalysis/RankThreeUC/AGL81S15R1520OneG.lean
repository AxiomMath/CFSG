module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalCores CFSG.RankThree.PartOne.Sec1511

theorem not_dvd_card_generalizedFitting {Y : Type} [Group Y] [Finite Y] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hO : CFSG.pPrimeCore p Y = ⊥)
    (hK : ∀ K : Subgroup Y, CFSG.IsComponent K → ¬ q ∣ Nat.card K) :
    ¬ q ∣ Nat.card (CFSG.generalizedFitting Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hF : CFSG.fittingSubgroup Y ≤ CFSG.pPrimeCore q Y := by
    rw [CFSG.Fitting_eq_pcore Y p hO]
    refine le_pPrimeCore_of_isSubnormal_p (CFSG.pCore_normal (p := p) (G := Y)).isSubnormal ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := p) (G := Y))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hq hp).2 hpq.symm)
  have hE : CFSG.layer Y ≤ CFSG.pPrimeCore q Y := sSup_le fun K hKc =>
    le_pPrimeCore_of_isSubnormal_p hKc.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 (hK K hKc))
  have hle : CFSG.generalizedFitting Y ≤ CFSG.pPrimeCore q Y := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact sup_le hF hE
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 CFSG.pPrimeCore_coprime_card
    (hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem generalizedFitting_cases_of_pRank_le_one {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hO : CFSG.pPrimeCore p Y = ⊥)
    (hr : CFSG.Open.pRank p (CFSG.generalizedFitting Y) ≤ 1) :
    (CFSG.generalizedFitting Y = CFSG.pCore p Y ∧ IsCyclic (CFSG.pCore p Y)) ∨
      (CFSG.pCore p Y = ⊥ ∧ ∃ K : Subgroup Y, CFSG.IsComponent K ∧
        CFSG.generalizedFitting Y = K ∧ Subgroup.center K = ⊥) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hFs : CFSG.generalizedFitting Y = CFSG.pCore p Y ⊔ CFSG.layer Y := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Y p hO]
  have hcyc2 : ∀ x y : Y, x ∈ CFSG.generalizedFitting Y → y ∈ CFSG.generalizedFitting Y →
      orderOf x = p → orderOf y = p → Commute x y → y ∈ Subgroup.zpowers x := by
    intro x y hx hy hxp hyp hxy
    by_contra hyx
    have := CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxp hyp hxy hyx
    omega
  have hcomm : ∀ {A B : Subgroup Y}, ⁅A, B⁆ = ⊥ → ∀ a ∈ A, ∀ b ∈ B, Commute a b :=
    fun h a ha b hb => (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha) b hb).symm
  by_cases hex : ∃ K : Subgroup Y, CFSG.IsComponent K
  swap
  ·
    push Not at hex
    have hFeq : CFSG.generalizedFitting Y = CFSG.pCore p Y := by
      rw [hFs, layer_eq_bot_of_forall hex, sup_bot_eq]
    exact Or.inl ⟨hFeq, CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2 hFeq.ge
      CFSG.pCore_isPGroup ((CFSG.SectionRank.pRank_coe_eq_openPRank p _).trans_le hr)⟩
  obtain ⟨K, hK⟩ := hex
  have hKF : ∀ {L : Subgroup Y}, CFSG.IsComponent L → L ≤ CFSG.generalizedFitting Y :=
    fun hL => (component_le_layer hL).trans (hFs ▸ le_sup_right)
  have hZ : Subgroup.center K = ⊥ := by
    have hrK : CFSG.pRank p ↥(⊤ : Subgroup K) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.SectionRank.pRank_mono hp.one_lt (hKF hK)).trans hr
    obtain ⟨S⟩ : Nonempty (Sylow p K) := inferInstance
    have hS : IsCyclic (S : Subgroup K) :=
      CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2 le_top S.isPGroup' hrK
    have hpZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
      intro hdvd
      obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hdvd
      rw [Subgroup.orderOf_mk] at hz
      refine CFSG.LocalAnalysis.RankThreeTheoremC.not_isCyclic_sylow_of_isPerfect hK.1.1 S hzZ
        ?_ (hz ▸ pow_orderOf_eq_one z) hS
      rintro rfl
      rw [orderOf_one] at hz
      exact hp.one_lt.ne hz
    have hle := le_pPrimeCore_of_isSubnormal_p
      ((Subgroup.Normal.isSubnormal inferInstance).trans' hK.2 :
        ((Subgroup.center K).map K.subtype).IsSubnormal) (by
          rw [Subgroup.card_map_of_injective K.subtype_injective]
          exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpZ)
    rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle
  have hcen : ∀ y ∈ K, (∀ k ∈ K, Commute k y) → y = 1 := by
    intro y hy hc
    have hyZ : (⟨y, hy⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.2 fun k => Subtype.ext (hc k k.2)
    rw [hZ, Subgroup.mem_bot] at hyZ
    exact congrArg Subtype.val hyZ
  obtain ⟨y, hyK, hyp, hy1⟩ := exists_pElement_component hO hK
  have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
  have hnot : ∀ {A : Subgroup Y}, ⁅A, K⁆ = ⊥ → ∀ x ∈ A, x ∈ CFSG.generalizedFitting Y →
      orderOf x = p → False := by
    intro A hAK x hxA hxF hxo
    refine hy1 (hcen y hyK fun k hk => ?_)
    have hyA : y ∈ A := Subgroup.zpowers_le.2 hxA
      (hcyc2 x y hxF (hKF hK hyK) hxo hyo (hcomm hAK x hxA y hyK))
    exact (hcomm hAK y hyA k hk).symm
  have hE : CFSG.layer Y = K := by
    refine le_antisymm (sSup_le fun L hL => ?_) (component_le_layer hK)
    rcases distinct_components_commute hL hK with h | h
    · exact h.le
    obtain ⟨x, hxL, hxp, hx1⟩ := exists_pElement_component hO hL
    exact (hnot h x hxL (hKF hL hxL) (orderOf_eq_prime hxp hx1)).elim
  have hP : CFSG.pCore p Y = ⊥ := by
    by_contra hne
    have hPK : ⁅CFSG.pCore p Y, K⁆ = ⊥ := by
      have := fitting_layer_commute (G := Y)
      rwa [CFSG.Fitting_eq_pcore Y p hO, hE] at this
    have hdvd : p ∣ Nat.card (CFSG.pCore p Y) :=
      (CFSG.pCore_isPGroup (p := p) (G := Y)).card_eq_or_dvd.resolve_left
        fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1)
    obtain ⟨⟨x, hxP⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := CFSG.pCore p Y) p hdvd
    rw [Subgroup.orderOf_mk] at hx
    exact hnot hPK x hxP (hFs ▸ Subgroup.mem_sup_left hxP) hx
  refine Or.inr ⟨hP, K, hK, ?_, hZ⟩
  rw [hFs, hP, hE, bot_sup_eq]

end CFSG.LocalAnalysis.RankThreeUC.S15
