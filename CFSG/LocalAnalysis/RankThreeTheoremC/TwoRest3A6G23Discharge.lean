module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6G23Cited
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111B3
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Prop3
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQShape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem block_facts (hk : D1CaseTwoKFacts3 G) {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} {z : H}
    {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    M ≤ Subgroup.normalizer (L : Set G) ∧ (centBase M R L hRM).relIndex R ≤ 3 := by
  obtain ⟨h, hzM, -, hz3, hCz, hrk, hcyc, hin⟩ := D1CaseTwoData3.nf_inputs hk.out hk.seitzCyc
    hk.caseTwoLocal hk.inv hk.schreier hk.sylow hk.eightFour hk.eightFive hk.eightSix
    hk.nineThree hk.noXBlock hk.toralThree cfg.data cfg.cand cfg.notSP cfg.outside cfg.b0
    cfg.normalizer_le
  have hRP : R ≤ (P : Subgroup G) := h.toD1Escape.le_P
  have hidx := TwoRest3A6.index_centralizer_barM_le_three h kFactBlockThreeASix_holds
    hk.eightFive hk.eightSix hk.nineThree hk.noXBlock hcyc hzM hz3 hCz hin hrk cfg.block cfg.center
    cfg.quot cfg.centV cfg.notShort hRP
  refine ⟨?_, ?_⟩
  · have hnorm : (L.subgroupOf M).Normal :=
      TwoRest3A6.normal_of_threeASix h kFactBlockThreeASix_holds hcyc hzM hz3 hCz hin hrk cfg.b0 hRM
        cfg.block cfg.center cfg.quot hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer cfg.block.le).mp hnorm
  · have e : (centBase M R L hRM).subgroupOf R =
        (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp
          (Subgroup.inclusion (hRP.trans h.toD1Escape.sylow_le))) :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    show ((centBase M R L hRM).subgroupOf R).index ≤ 3
    rw [e]
    exact hidx

theorem exists_normalCyclic_lift {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoDataU p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) :
    ∃ S : Subgroup G, S ≤ R ∧ (∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) ∧ IsCyclic S ∧
      p < Nat.card S ∧
      (S.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hL hLX
  obtain ⟨TL, hTL⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  set D : Subgroup (H ⧸ primeComplementCore (G := H) p) := (Rbar : Subgroup _) ⊓ L with hD
  have hDcard : p ^ 2 ≤ Nat.card D := by
    have h1 : Nat.card D = Nat.card (TL : Subgroup L) := by
      rw [← hTL, Subgroup.card_map_of_injective L.subtype_injective]
    rw [h1]
    exact hSyl p L hiso TL
  have hDnorm : ∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), ∀ x ∈ D,
      r * x * r⁻¹ ∈ D := by
    rintro r hr x ⟨hxR, hxL⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hxR) (Subgroup.inv_mem _ hr), ?_⟩
    have hrN : r ∈ Subgroup.normalizer (L : Set _) := by
      simpa using hd.cfg.red.conj_mem_normalizer_component hL hr 1
    exact (Subgroup.mem_normalizer_iff.mp hrN x).mp hxL
  have hRH : R ≤ H := hd.cfg.ext.le_H
  obtain ⟨S, hSH, hSR, hSmap, hSall, ψ, -⟩ := exists_lift_of_le_map hp hRH hd.cfg.ext.isPGroup
    (primeComplementCore (G := H) p) (primeComplementCore_coprime p) (Sbar := D)
    (inf_le_left.trans hd.cfg.rbar.le)
  refine ⟨S, hSR, ?_, ?_, ?_, hSmap⟩
  · intro r hr s hs
    have hrH : r ∈ H := hRH hr
    have hsH : s ∈ H := hSH hs
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) p)
        (⟨r, hrH⟩ * ⟨s, hsH⟩ * ⟨r, hrH⟩⁻¹) ∈ D := by
      rw [map_mul, map_mul, map_inv]
      refine hDnorm _ ?_ _ ?_
      · rw [hd.cfg.rbar]
        exact Subgroup.mem_map_of_mem _ (show (⟨r, hrH⟩ : H) ∈ R.subgroupOf H from hr)
      · rw [← hSmap]
        exact Subgroup.mem_map_of_mem _ (show (⟨s, hsH⟩ : H) ∈ S.subgroupOf H from hs)
    exact hSall (⟨r, hrH⟩ * ⟨s, hsH⟩ * ⟨r, hrH⟩⁻¹)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr (hSR hs)) (Subgroup.inv_mem _ hr)) hmem
  · exact (ψ.isCyclic).mpr (hd.cyclic L hL)
  · rw [Nat.card_congr ψ.toEquiv]
    exact lt_of_lt_of_le (by nlinarith [hp.two_le]) hDcard

theorem exists_mem_base_inf_component (hk : D1CaseTwoKFacts3 G) {P : Sylow 3 G}
    {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData3 3 P M H R Rbar) {B : Subgroup G} (hidx : B.relIndex R ≤ 3)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 3 M H) :
    ∃ q : H, (q : G) ∈ B ∧ QuotientGroup.mk' (primeComplementCore (G := H) 3) q ∈ L ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := H) 3) q) = 3 ∧
      ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ (q : G) ∈ E := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hRH : R ≤ H := hd.cfg.ext.le_H
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.le_P
  obtain ⟨S, hSR, hSnorm, hScyc, hSc, hSmap⟩ :=
    exists_normalCyclic_lift hk.out hk.seitzCyc hk.sylow hd.toU hL hLX
  haveI : IsCyclic S := hScyc
  have hrelS : B.relIndex S ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hSR
      (CFSG.GH74.Uniqueness.SU.SU1.relIndex_ne_zero_of_finite B R)).trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := B) (K := S)
  have hSp : IsPGroup 3 S := hd.cfg.ext.isPGroup.to_le hSR
  have hBSp : IsPGroup 3 (B ⊓ S : Subgroup G) := hSp.to_le inf_le_right
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hBSp
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    rw [hj] at hmul
    have : Nat.card S ≤ 3 := by omega
    omega
  have hdvd : 3 ∣ Nat.card (B ⊓ S : Subgroup G) := by
    rw [hj]
    exact dvd_pow_self 3 hj0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hq₀B : (x : G) ∈ B := x.2.1
  have hq₀S : (x : G) ∈ S := x.2.2
  have hqo : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  have hq₀R : (x : G) ∈ R := hSR hq₀S
  set q : H := ⟨(x : G), hRH hq₀R⟩
  have hoq : orderOf q = 3 := (Subgroup.orderOf_coe q).symm.trans hqo
  have hqL : QuotientGroup.mk' (primeComplementCore (G := H) 3) q ∈ L := by
    have : QuotientGroup.mk' (primeComplementCore (G := H) 3) q ∈
        (S.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) :=
      ⟨q, Subgroup.mem_subgroupOf.mpr hq₀S, rfl⟩
    rw [hSmap] at this
    exact this.2
  obtain ⟨E, hER, hE, hEcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    hp hd.cfg.ext.three_le_pRank
  have hEc : Nat.card E = 27 := by rw [hEcard]; norm_num
  refine ⟨q, hq₀B, hqL, orderOf_mk_of_coprime hp (primeComplementCore (G := H) 3)
    (primeComplementCore_coprime 3) hoq, E, hER, hE, hEc, ?_⟩
  by_contra hqE
  have hq3 : (x : G) ^ 3 = 1 := by rw [← hqo]; exact pow_orderOf_eq_one _
  have hC : (x : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heR : e ∈ R := hER he
    have h1 : e * (x : G) * e⁻¹ ∈ Subgroup.zpowers (x : G) :=
      conj_mem_zpowers_of_isCyclic (T := S) rfl hq₀S (hSnorm e heR _ hq₀S)
    exact (commute_of_mem_normalizer_zpowers_of_pow_eq_one hp hqo
      (mem_normalizer_zpowers_of_mem_zpowers h1) (hE.2 e he)).eq
  have h4 := succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hE (k := 3) hEcard hq3 hqE hC
    hER hq₀R
  have h5 : Open.pRank 3 (R : Subgroup G) ≤ 3 :=
    (pRank_mono 3 hp hRP).trans hd.cfg.pRank_eq_three.le
  omega

theorem normalizer_zpowers_le_of_tenFourteen (hk : D1CaseTwoKFacts3 G)
    (h1014 : TwoRestTenFourteen G) {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} {z : H}
    {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    ∀ a ∈ centBase M R L hRM, a ≠ 1 → a ^ 3 = 1 →
      (∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ a ∈ E) →
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M := by
  intro a ha ha1 ha3 hE
  obtain ⟨hMN, -⟩ := block_facts hk cfg hRM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he := cfg.data.cfg.ext.toD1Escape
  obtain ⟨E, hER, hEab, hEc, haE⟩ := hE
  have hCM : Subgroup.centralizer ({a} : Set G) ≤ M := by
    by_contra hCM
    apply h1014 P M H R Rbar z Kbar L cfg a ha1 ha3 ⟨E, hER, hEab, hEc, haE⟩ hCM
    rw [Subgroup.commutator_le]
    intro g hg l hl
    rw [commutatorElement_def]
    have hgB : g ∈ centBase M R L hRM := (Subgroup.zpowers_le.mpr ha) hg
    have hgM : g ∈ M := hRM (centBase_le hRM hgB)
    have h1 : g * l * g⁻¹ * l⁻¹ ∈ pCoreOf 2 M := centBase_comm hRM cfg.block.le g hgB l hl
    have h2 : g * l * g⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMN hgM) l).mp hl) (L.inv_mem hl)
    exact inf_le_pCoreOf cfg.block.le ⟨h2, h1⟩
  exact normalizer_zpowers_le he.sylow_le he.weakCore_le haE hEab (hEc.trans (by norm_num)) hCM

theorem rankThreeGamma_zpowers_le {M : Subgroup G} {a : G} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (hN : Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M) :
    rankThreeGamma 1 3 (Subgroup.zpowers a) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQF, hQr, rfl⟩
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    have := CFSG.SectionRank.pRank_le (p := 3) (k := 0) (H := (⊥ : Subgroup G)) (by norm_num)
      (fun E hE _ => by rw [le_bot_iff.mp hE, Subgroup.card_bot]; norm_num)
    omega
  have hzc : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hQc : Nat.card Q = 3 := by
    have hd : Nat.card Q ∣ 3 := hzc ▸ Subgroup.card_dvd_of_le hQF
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq Q h1) hQ1
    · exact h3
  have hQ : Q = Subgroup.zpowers a := Subgroup.eq_of_le_of_card_ge hQF (by rw [hQc, hzc])
  rw [hQ]
  exact hN

theorem le_X0_of_tenFourteen (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {z : H} {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M)
    {L' : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL' : IsComponentOf L' ⊤)
    (hne : Kbar ≠ L') : L' ≤ d1X0 3 M H := by
  by_contra hL'X
  obtain ⟨-, hidx⟩ := block_facts hk cfg hRM
  obtain ⟨q, hqB, hqK, hqo, E, hER, hE, hEc, hqE⟩ :=
    exists_mem_base_inf_component hk cfg.data hidx cfg.component cfg.not_le
  have hq3 : (q : G) ^ 3 = 1 := hE.2 _ hqE
  have hq1 : (q : G) ≠ 1 := by
    intro h
    have : q = 1 := Subtype.ext h
    rw [this, map_one, orderOf_one] at hqo
    exact absurd hqo (by norm_num)
  have hN := normalizer_zpowers_le_of_tenFourteen hk h1014 cfg hRM (q : G) hqB hq1 hq3
    ⟨E, hER, hE, hEc, hqE⟩
  have hEL : ((Subgroup.zpowers (q : G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ Kbar ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) 3) q ∈
        ((Subgroup.zpowers (q : G)).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ Kbar :=
      ⟨⟨q, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _), rfl⟩, hqK⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hqo
    exact absurd hqo (by norm_num)
  exact InnerQ.not_gamma_le_of_two_components Nat.prime_three cfg.component hL' hne hL'X
    (isElemAbelian_zpowers hq3) hEL (rankThreeGamma_zpowers_le hq1 hq3 hN)

theorem nineThree_b3_of_tenFourteen (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {z : H} {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    Hyp111NineThree 3 M H Kbar ∧ Hyp111B3 3 H (centBase M R L hRM) Kbar := by
  obtain ⟨-, hidx⟩ := block_facts hk cfg hRM
  have hd := cfg.data
  have hA := hd.cfg.red.cycAutRankLeTwo_of_kFactOutCyclic hd.cfg.catalog hk.out
  have hK : IsCaseTwoGroup 3 Kbar :=
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hk.out hk.seitzCyc hd.cyclic hd.rank
      cfg.component cfg.not_le
  obtain ⟨q, hqB, hqK, hqo, -⟩ := exists_mem_base_inf_component hk hd hidx cfg.component cfg.not_le
  have h93 : Hyp111NineThree 3 M H Kbar := by
    by_cases huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ →
        L = Kbar
    · exact nineThree_of_caseTwo_unique hd hA cfg.component huniq
    · push Not at huniq
      obtain ⟨L₂, h₂, hne⟩ := huniq
      exact nineThree_of_caseTwo_mixed hd cfg.component h₂ cfg.not_le
        (le_X0_of_tenFourteen hk h1014 cfg hRM h₂ hne.symm)
  haveI := h93.normal
  exact ⟨h93, b3_of_normal hk.noTwo hK ⟨q, hqB, hqK, hqo⟩⟩

theorem innerNotQJ_eq_of_tenFourteen (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {z : H} {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    innerNotQJ 3 H Kbar = Kbar := by
  haveI := (nineThree_b3_of_tenFourteen hk h1014 cfg hRM).1.normal
  exact innerNotQJ_eq_of_normal 3 H Kbar

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23

