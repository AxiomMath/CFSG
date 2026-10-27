module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.BetaPrimes
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.AGL81TheoremCD.FrobeniusRank
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

variable {G : Type} [Group G] [Finite G]

theorem sigmaA_eq_uniqueFourBeta (hS : Standing4 G) :
    rankThreeSigmaA G = uniqueFourBeta G := by
  rw [CFSG.AGLEmbedding.sigmaA_eq_betaFour (le_trans (by norm_num) hS.rank)]
  rfl

theorem mem_uniqueFourSigma_of_two_le_pRank (hU : uniqueFourUnique G)
    {N : Subgroup G} (hN : uniqueFourIsMaxTwoLocal N) {p : ℕ}
    (hp : p ∈ uniqueFourBeta G) (h2 : 2 ≤ Open.pRank p N) : p ∈ uniqueFourSigma N := by
  haveI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨E, hEN, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) h2
  obtain ⟨N', hN', hpN'⟩ := exists_maxLocal_mem_sigma hp
  obtain ⟨P, hPN', -⟩ := exists_sylow_le_of_sigma hU hN' hpN'
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow (IsElemAbelian.isPGroup hEel) P
  have hEN' : E ≤ uniqueFourConj g N' := hg.trans (uniqueFourConj_mono hPN' g)
  have hE2 : 2 ≤ Open.pRank p E := le_pRank_of_elemAbelian (k := 2) hp.1 le_rfl hEel hEcard
  have hN'g : uniqueFourIsMaxTwoLocal (uniqueFourConj g N') := isMaxTwoLocal_conj hN' g
  have hpN'g : p ∈ uniqueFourSigma (uniqueFourConj g N') := mem_uniqueFourSigma_conj hpN' g
  have hle : N ≤ uniqueFourConj g N' := sec61 hU hN'g hpN'g hEN' hE2 hN.1 hEN
  have heq : uniqueFourConj g N' = N := hN.2 _ hN'g.1 hle
  rw [← heq]
  exact hpN'g

theorem sigmaM_eq_uniqueFourSigma (hS : Standing4 G) (hU : uniqueFourUnique G)
    {N : Subgroup G} (hN : uniqueFourIsMaxTwoLocal N) :
    sigmaSet G N = uniqueFourSigma N := by
  ext p
  constructor
  · rintro ⟨hpA, h2⟩
    have hpβ : p ∈ uniqueFourBeta G := (sigmaA_eq_uniqueFourBeta hS) ▸ hpA
    exact mem_uniqueFourSigma_of_two_le_pRank hU hN hpβ h2
  · intro hp
    refine ⟨?_, le_trans (by norm_num) (four_le_pRank_of_sigma hp)⟩
    rw [sigmaA_eq_uniqueFourBeta hS]
    exact hp.1

private theorem uniqueFourPrimeCore_pRank_le_one {N P₀ : Subgroup G} {p q : ℕ}
    (hfrob : uniqueFourIsFrobenius (uniqueFourPrimeCore p N ⊔ P₀)
      (pCoreOf 2 N) (uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀))
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (rankThreePrimeCore p N) ≤ 1 := by
  obtain ⟨hKne, -, hKX, hKnorm, hVX, hRsup, hdisj, hfpf⟩ := hfrob
  have hK2 : IsPGroup 2 (pCoreOf 2 N) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  exact pRank_le_one_of_twoGroup_frobeniusSup hK2 hKne hKX hVX le_sup_left hKnorm
    hRsup hdisj (hVX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnorm))
    hfpf hq hq2

private theorem pRank_le_one_of_cyclic_pSubgroups {p : ℕ} (hp : p.Prime)
    {R : Subgroup G} (hcyc : ∀ S : Subgroup G, S ≤ R → IsPGroup p S → IsCyclic S) :
    CFSG.Open.pRank p R ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt (H := R) (k := 1) ?_
  intro E hE hEel
  have hEcyc : IsCyclic ↥E := hcyc E hE hEel.isPGroup
  haveI : IsCyclic ↥E := hEcyc
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic E)
  have hcard : Nat.card E = orderOf x := (orderOf_eq_card_of_zpowers_eq_top hx).symm
  have hxq : x ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hEel.2 (x : G) x.2
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxq
  have hcardp : Nat.card ↥E ≤ p := by
    rw [hcard]
    exact Nat.le_of_dvd hp.pos hdvd
  simpa [pow_one] using hcardp

private theorem uniqueFourLayer_centralizer_pRank_le_one_of_ne {N P₀ : Subgroup G} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hP₀card : Nat.card P₀ = p)
    (hcyclic : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) →
      IsPGroup p S → IsCyclic S)
    (hfrob : uniqueFourIsFrobenius (uniqueFourPrimeCore p N ⊔ P₀) (pCoreOf 2 N)
      (uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀)) :
    CFSG.Open.pRank q (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hKne, -, hKX, hKnorm, hVX, -, -, hfpf⟩ := hfrob
  have hK2 : IsPGroup 2 (pCoreOf 2 N) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  have hVnorm : uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀ ≤
      Subgroup.normalizer (pCoreOf 2 N : Set G) :=
    hVX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnorm)
  have hVrank : CFSG.Open.pRank q
      (uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀) ≤ 1 :=
    pRank_le_one_of_twoGroup_fixedPointFree hK2 hKne hVnorm hfpf hq hq2
  have hRleV : CFSG.Open.relPPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ≤
      uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀ := le_sup_left
  have hcoreRank : CFSG.Open.pRank q
      (CFSG.Open.relPPrimeCore p (Subgroup.centralizer (P₀ : Set G))) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hq.one_lt hRleV).trans hVrank
  refine CFSG.SectionRank.pRank_le hq.one_lt (H := Subgroup.centralizer (P₀ : Set G) ⊓
    Subgroup.centralizer
      (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) (k := 1) ?_
  intro E hE hEel
  have hEcore : E ≤ CFSG.Open.relPPrimeCore p
      (Subgroup.centralizer (P₀ : Set G)) :=
    qSubgroup_le_relPPrimeCore_of_cyclic_pSubgroups hp hq hqp rfl hP₀card
      (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLayer_le _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLayer_le _)).mpr
        (CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_rankThreeLayer _))
      rfl hcyclic hE hEel.isPGroup
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEel).exists_card_eq
  have hnle : n ≤ CFSG.Open.pRank q
      (CFSG.Open.relPPrimeCore p (Subgroup.centralizer (P₀ : Set G))) :=
    CFSG.SectionRank.le_pRank hq.one_lt hEcore hEel hn
  have hn1 : n ≤ 1 := hnle.trans hcoreRank
  have hcard : Nat.card ↥E ≤ q := by
    calc Nat.card ↥E = q ^ n := hn
      _ ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hn1
      _ = q := pow_one q
  simpa [pow_one] using hcard

private theorem uniqueFourLayer_centralizer_pRank_le_one {N P₀ : Subgroup G} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hP₀card : Nat.card P₀ = p)
    (hcyclic : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) →
      IsPGroup p S → IsCyclic S)
    (hfrob : uniqueFourIsFrobenius (uniqueFourPrimeCore p N ⊔ P₀) (pCoreOf 2 N)
      (uniqueFourPrimeCore p (Subgroup.centralizer (P₀ : Set G)) ⊔ P₀)) :
    CFSG.Open.pRank q (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1 := by
  by_cases hqp : q = p
  · subst q
    exact pRank_le_one_of_cyclic_pSubgroups hp hcyclic
  · exact uniqueFourLayer_centralizer_pRank_le_one_of_ne hp hq hq2 hqp hP₀card hcyclic hfrob

theorem almostStrongCore_of_uniqueFourAlmostStrong {N : Subgroup G} {p : ℕ}
    (h : uniqueFourAlmostStrong N p) : AlmostStrongCore N p := by
  obtain ⟨hpβ, hNne, -, P, hPN, hΓ, hcase⟩ := h
  refine ⟨P, hPN, ?_, ?_⟩
  · simpa [rankThreeGamma, uniqueFourGamma] using hΓ
  · rcases hcase with ⟨hdvd, hstrong⟩ | ⟨h5, hsolv, -, P₀, hP₀⟩
    · haveI : Fact p.Prime := ⟨hpβ.1⟩
      have hPne : (P : Subgroup G) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := G) (p := p) P hpβ.2.2.1
      have hstr := isStronglyPEmbedded_of_clause_one hNne hdvd hstrong
      exact Or.inl (by
        rw [CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPN hNne hPne]
        exact hstr)
    · obtain ⟨hP₀P, hP₀card, hclosed, hiso, hnotle, hcyclic, hfrob, hother⟩ := hP₀
      refine Or.inr (Or.inl ⟨h5, hsolv, P₀, hP₀P, hP₀card, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      · exact hclosed
      · exact hiso
      · exact hnotle
      · exact hother
      · intro q hq hq2
        exact uniqueFourPrimeCore_pRank_le_one hfrob hq hq2
      · intro q hq hq2
        exact uniqueFourLayer_centralizer_pRank_le_one hpβ.1 hq hq2 hP₀card hcyclic hfrob

theorem cStarGen_of_unique4 (hS : Standing4 G) (hU : uniqueFourUnique G) : CStarGen G where
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  charTwo := hS.charTwo
  rank := le_trans (by norm_num) hS.rank
  embed := by
    intro p hp N hN Q hQN hQ hQ2 H hH hQH
    exact le_of_mem_uniqueFourBeta hU hN ((sigmaA_eq_uniqueFourBeta hS) ▸ hp) hQN hQ hQ2 hH hQH
  exists_maxLocal := by
    intro p hp
    have hpβ : p ∈ uniqueFourBeta G := (sigmaA_eq_uniqueFourBeta hS) ▸ hp
    obtain ⟨N, hN, hpN⟩ := exists_maxLocal_mem_sigma hpβ
    refine ⟨N, hN, ?_⟩
    rw [sigmaM_eq_uniqueFourSigma hS hU hN]
    exact hpN
  almost := by
    intro N hN p hp
    rw [sigmaM_eq_uniqueFourSigma hS hU hN] at hp
    exact almostStrongCore_of_uniqueFourAlmostStrong ((hU N hN ⟨p, hp⟩).1 p hp)
  off_sigma := by
    intro p hpPrime hp2 hpNot
    refine ⟨?_, fun _ => Or.inl hS.rank⟩
    by_contra hle
    have h4 : 4 ≤ rankThreeLocalRank p G := by omega
    obtain ⟨H, -, hHrank⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_attained (G := G) p (by omega)
    have hpPos : 0 < Open.pRank p H := by rw [hHrank]; omega
    have hdvd : p ∣ Nat.card G :=
      CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos p H hpPos
    have hpβ : p ∈ uniqueFourBeta G :=
      ⟨hpPrime, hp2, hdvd, by
        simpa [CFSG.Open.uniqueFourTwoLocalRank, CFSG.Open.rankThreeLocalRank] using h4⟩
    exact hpNot (by
      rw [sigmaA_eq_uniqueFourBeta hS]
      exact hpβ)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
