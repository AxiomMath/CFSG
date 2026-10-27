module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank

import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q p : ℕ}
  {E : Subgroup G}

structure Hyp1417 (G : Type) [Group G] [Finite G] (M : Subgroup G) (q p : ℕ)
    (E : Subgroup G) : Prop where
  cstar : CStarGen G
  maxLocal : CFSG.Open.rankThreeIsMaxTwoLocal M
  sigma_ne : (sigmaSet G M).Nonempty
  strong : ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M
  hq : q ∈ sigmaM G M
  hp : p.Prime
  hp2 : p ≠ 2
  hpq : p ≠ q
  le : E ≤ M
  elem : IsElemAbelian p E
  card : Nat.card E = p ^ 2
  dvd : q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G))
  rank : ∀ A : Subgroup G, A ≤ E → Nat.card A = p →
    2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G))

structure Setting1417 (G : Type) [Group G] [Finite G] (M Q H F : Subgroup G) (q : ℕ) :
    Prop where
  cstar : CStarGen G
  maxLocal : CFSG.Open.rankThreeIsMaxTwoLocal M
  strong : ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M
  hq : q ∈ sigmaM G M
  nine : AGL81C.NineSettingGen G M q Q H F 2
  sylowH : CFSG.ABGLocalTools.IsSylowOf q Q H
  sylowHM : CFSG.ABGLocalTools.IsSylowOf q Q (H ⊓ M)

theorem Hyp1417.qPrime (h : Hyp1417 G M q p E) : q.Prime :=
  CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q h.hq.1

theorem Hyp1417.q_ne_two (h : Hyp1417 G M q p E) : q ≠ 2 := by
  have hodd := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd q h.hq.1
  rintro rfl
  exact hodd rfl

theorem Setting1417.qPrime (s : Setting1417 G M Q H F q) : q.Prime :=
  s.nine.prime

theorem Setting1417.q_ne_two (s : Setting1417 G M Q H F q) : q ≠ 2 :=
  s.nine.ne_two

theorem Setting1417.strongQ (s : Setting1417 G M Q H F q) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded q M :=
  s.strong q (by simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using s.hq)

theorem Setting1417.not_le (s : Setting1417 G M Q H F q) : ¬ H ≤ M :=
  s.nine.not_le

theorem Setting1417.Q_le_M (s : Setting1417 G M Q H F q) : Q ≤ M :=
  s.nine.Q_le_M

theorem Setting1417.two_le_pRank_Q (s : Setting1417 G M Q H F q) :
    2 ≤ CFSG.Open.pRank q Q :=
  AGL81C.QSet.two_le_pRank_of_mem s.nine.mem_Q

private theorem Hyp1417.normalizer_ne_top (h : Hyp1417 G M q p E) {A : Subgroup G}
    (hAE : A ≤ E) (hA : Nat.card A = p) : Subgroup.normalizer (A : Set G) ≠ ⊤ := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hAlt : Nat.card A < Nat.card E := by
    rw [hA, h.card, pow_two]
    calc p = p * 1 := (mul_one p).symm
      _ < p * p := Nat.mul_lt_mul_of_pos_left h.hp.one_lt (Nat.Prime.pos h.hp)
  have hAne_bot : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hA
    exact h.hp.ne_one hA.symm
  have hAne_top : A ≠ ⊤ := by
    intro htop
    have hEtop : E = ⊤ := top_unique (htop ▸ hAE)
    rw [htop, hEtop] at hAlt
    exact lt_irrefl _ hAlt
  intro hHtop
  have hAn : A.Normal := Subgroup.normalizer_eq_top_iff.mp hHtop
  letI : A.Normal := hAn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with hbot | htop
  · exact hAne_bot hbot
  · exact hAne_top htop

theorem Hyp1417.exists_setting (h : Hyp1417 G M q p E) {A : Subgroup G} (hAE : A ≤ E)
    (hA : Nat.card A = p) (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M) :
    ∃ Q F : Subgroup G, Setting1417 G M Q (Subgroup.normalizer (A : Set G)) F q := by
  classical
  haveI : Fact q.Prime := ⟨h.qPrime⟩
  have hqSet : q ∈ sigmaSet G M := by
    simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.hq
  obtain ⟨Q, hQ⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf q (Subgroup.normalizer (A : Set G) ⊓ M)
  have hQrank : 2 ≤ CFSG.Open.pRank q Q := by
    rw [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow h.qPrime hQ]
    simpa only [inf_comm] using h.rank A hAE hA
  obtain ⟨F, hFQ, hFea, hFcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (k := 2) hQrank
  have hFM : F ≤ M := hFQ.trans (hQ.le.trans inf_le_right)
  have hΓ : CFSG.Open.rankThreeGamma 1 q F ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_self_le
      (h.strong q hqSet) hFM hFea.isPGroup
  have hHne : Subgroup.normalizer (A : Set G) ≠ ⊤ :=
    h.normalizer_ne_top hAE hA
  have hsigma : (sigmaM G M).Nonempty := by
    obtain ⟨r, hr⟩ := h.sigma_ne
    exact ⟨r, by simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hr⟩
  have hnine : AGL81C.NineSettingGen G M q Q (Subgroup.normalizer (A : Set G)) F 2 :=
    { setting := ⟨h.cstar, h.maxLocal, hsigma⟩
      mem_Q := AGL81C.mem_QSet_iff.mpr ⟨h.qPrime, h.q_ne_two,
        hQ.le.trans inf_le_right, hQ.isPGroup, Or.inr ⟨F, hFQ, hFea, hFcard, hΓ⟩⟩
      mem_H := AGL81C.mem_HFam_iff.mpr
        ⟨hHne, hQ.le.trans inf_le_left, hH⟩
      stdE := ⟨Or.inl rfl, hFQ, hFea, hFcard, hΓ⟩ }
  have hSylowH : CFSG.ABGLocalTools.IsSylowOf q Q (Subgroup.normalizer (A : Set G)) :=
    (hnine.isSylowOf_of_isSylowOf_inf h.hq hQ).1
  exact ⟨Q, F, ⟨h.cstar, h.maxLocal, h.strong, h.hq, hnine, hSylowH, hQ⟩⟩

theorem Hyp1417.exists_orderOf_eq (h : Hyp1417 G M q p E) :
    ∃ y ∈ M ⊓ Subgroup.centralizer (E : Set G), orderOf y = q := by
  haveI : Fact q.Prime := ⟨h.qPrime⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := ↥(M ⊓ Subgroup.centralizer (E : Set G))) q h.dvd
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe, hy]⟩

theorem Setting1417.normalizer_le_of_isPGroup (s : Setting1417 G M Q H F q) {W : Subgroup G}
    (hW : W ≠ ⊥) (hWq : IsPGroup q W) (hWM : W ≤ M) :
    Subgroup.normalizer (W : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  exact s.strongQ.normalizer_le hW hWq hWM

theorem Setting1417.odd_card_relPPrimeCore (s : Setting1417 G M Q H F q) :
    Odd (Nat.card (CFSG.Open.relPPrimeCore q H)) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := CFSG.Open.relPPrimeCore q H
  change Odd (Nat.card N)
  have hNH : N ≤ H := relPPrimeCore_le (p := q) H
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp
      (relPPrimeCore_normal
        s.qPrime H)
  have hQN : Q ≤ Subgroup.normalizer (N : Set G) := s.nine.Q_le_H.trans hHN
  have hnotdvd : ¬ q ∣ Nat.card N :=
    (s.qPrime.coprime_iff_not_dvd).mp (coprime_card_relPPrimeCore s.qPrime H)
  obtain ⟨T, hT, -, hQT⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (A := Q) (K := N) (P := ⊥)
      s.qPrime Nat.prime_two (AGL81C.QSet.isPGroup_of_mem s.nine.mem_Q) hQN hnotdvd bot_le
      (IsPGroup.of_bot (p := 2) (G := G))
      (by
        rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
        exact le_top)
  by_contra hnotodd
  have h2dvd : 2 ∣ Nat.card N := by
    rw [← even_iff_two_dvd]
    exact Nat.not_odd_iff_even.mp hnotodd
  have hpos : 0 < (Nat.card N).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (Nat.card_pos.ne') h2dvd
  have hTgt : 1 < Nat.card T := by
    rw [hT.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt hpos) (by norm_num)
  have hTne : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hTgt
    omega
  have h2loc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (T : Set G)) :=
    ⟨T, hTne, hT.isPGroup, rfl⟩
  have hNormT : Subgroup.normalizer (T : Set G) ≤ M :=
    s.cstar.embed q s.hq.1 M s.maxLocal Q s.nine.Q_le_M
      (AGL81C.QSet.isPGroup_of_mem s.nine.mem_Q)
      (AGL81C.QSet.two_le_pRank_of_mem s.nine.mem_Q) _ h2loc hQT
  have hfr := CFSG.RankThree.PartTwo.Sec18.le_sup_normalizer_of_isSylowOf hT hHN
  exact s.nine.not_le (hfr.trans (sup_le s.nine.relPPrimeCore_le hNormT))

theorem Setting1417.pCoreOf_two_eq_bot (s : Setting1417 G M Q H F q) :
    CFSG.Open.pCoreOf 2 H = ⊥ := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  have hle : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.relPPrimeCore q H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore
      s.q_ne_two H
  have hodd : Odd (Nat.card (CFSG.Open.pCoreOf 2 H)) :=
    Odd.of_dvd_nat s.odd_card_relPPrimeCore (Subgroup.card_dvd_of_le hle)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).exists_card_eq
  rw [hn] at hodd
  have hn0 : n = 0 := by
    by_contra hne
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    exact hodd.not_two_dvd_nat ⟨2 ^ m, by rw [pow_succ, mul_comm]⟩
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])

private theorem Setting1417.not_dvd_card_relPPrimeCore_of_mem_sigmaSet
    (s : Setting1417 G M Q H F q) {r : ℕ} (hr : r.Prime) (hrσ : r ∈ sigmaSet G M) :
    ¬ r ∣ Nat.card (CFSG.Open.relPPrimeCore q H) := by
  classical
  intro hdvd
  haveI : Fact r.Prime := ⟨hr⟩
  let N : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hNH : N ≤ H := relPPrimeCore_le (p := q) H
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp
      (relPPrimeCore_normal
        s.qPrime H)
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r N
  have hpos : 0 < (Nat.card N).factorization r :=
    hr.factorization_pos_of_dvd (Nat.card_pos.ne') hdvd
  have hRgt : 1 < Nat.card R := by
    rw [hR.card_eq]
    exact Nat.one_lt_pow (Nat.ne_of_gt hpos) hr.one_lt
  have hRne : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hRgt
    omega
  have hRM : R ≤ M := hR.le.trans s.nine.relPPrimeCore_le
  have hNormR : Subgroup.normalizer (R : Set G) ≤ M :=
    (s.strong r hrσ).normalizer_le hRne hR.isPGroup hRM
  have hfr : H ≤ N ⊔ Subgroup.normalizer (R : Set G) :=
    CFSG.RankThree.PartTwo.Sec18.le_sup_normalizer_of_isSylowOf hR hHN
  exact s.nine.not_le (hfr.trans (sup_le s.nine.relPPrimeCore_le hNormR))

theorem Setting1417.pRank_relPPrimeCore_le_three (s : Setting1417 G M Q H F q) {r : ℕ}
    (hr : r.Prime) : CFSG.Open.pRank r (CFSG.Open.relPPrimeCore q H) ≤ 3 := by
  by_cases hrq : r = q
  · subst r
    have hnot : ¬ q ∣ Nat.card (CFSG.Open.relPPrimeCore q H) :=
      (s.qPrime.coprime_iff_not_dvd).mp (coprime_card_relPPrimeCore s.qPrime H)
    rw [CFSG.LocalAnalysis.GLTheoremA.pRank_eq_zero_of_not_dvd_card s.qPrime hnot]
    exact Nat.zero_le 3
  · by_cases hr2 : r = 2
    · subst r
      have hnot : ¬ 2 ∣ Nat.card (CFSG.Open.relPPrimeCore q H) :=
        s.odd_card_relPPrimeCore.not_two_dvd_nat
      rw [CFSG.LocalAnalysis.GLTheoremA.pRank_eq_zero_of_not_dvd_card Nat.prime_two hnot]
      exact Nat.zero_le 3
    · by_cases hrσ : r ∈ sigmaSet G M
      · rw [CFSG.LocalAnalysis.GLTheoremA.pRank_eq_zero_of_not_dvd_card hr
          (s.not_dvd_card_relPPrimeCore_of_mem_sigmaSet hr hrσ)]
        exact Nat.zero_le 3
      · exact (CFSG.SectionRank.pRank_mono hr.one_lt s.nine.relPPrimeCore_le).trans
          (s.cstar.pRank_le_three_of_not_mem_sigmaSet s.maxLocal hr hr2 hrσ)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
