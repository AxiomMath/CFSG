module

public import CFSG.LocalAnalysis.AGL81TheoremCD.FourteenSixteen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem isTwoLocal_of_mem_H2StarFam [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hchar : IsCharTwoType G) {M E H : Subgroup G} (hE : E ≠ ⊥) (hH : H ∈ H2StarFam M E) :
    IsTwoLocal H := by
  have hO : pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    have hcen := hH.1.2.2.2
    rw [hbot] at hcen
    apply hE
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x ∈ H ⊓ centralizer ((⊥ : Subgroup G) : Set G) := by
      refine ⟨hH.1.2.1 hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy1 : y = 1 := by simpa using hy
      simp [hy1]
    exact hcen hx1
  have hK : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hO, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hHK : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hKmem : normalizer (pCoreOf 2 H : Set G) ∈ H2Fam M E :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hnonab _ hK,
      hH.1.2.1.trans hHK, fun hKM => hH.1.2.2.1 (hHK.trans hKM), hchar _ hK⟩
  exact ⟨pCoreOf 2 H, hO, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H,
    (hH.2 _ hKmem hHK).symm⟩

theorem exists_mem_H2StarFam_le {M E H₀ : Subgroup G} (hH₀ : H₀ ∈ H2Fam M E) :
    ∃ H ∈ H2StarFam M E, H₀ ≤ H := by
  obtain ⟨H, hmax⟩ := (Set.toFinite {H | H ∈ H2Fam M E ∧ H₀ ≤ H}).exists_maximal
    ⟨H₀, hH₀, le_rfl⟩
  exact ⟨H, ⟨hmax.1.1,
    fun H' hH' hle => le_antisymm (hmax.2 ⟨hH', hmax.1.2.trans hle⟩ hle) hle⟩, hmax.1.2⟩

structure HypCGen (G : Type) [Group G] [Finite G] (M : Subgroup G) (q : ℕ) (E H : Subgroup G) :
    Prop where
  cstar : CStarGen G
  maxLocal : CFSG.Open.rankThreeIsMaxTwoLocal M
  sigma_nonempty : (sigmaSet G M).Nonempty
  prime : q.Prime
  odd : q ≠ 2
  E_le_M : E ≤ M
  elem : CFSG.Open.IsElemAbelian q E
  card : Nat.card E = q ^ 2
  gamma : CFSG.Open.rankThreeGamma 1 q E ≤ M
  mem : H ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.H2StarFam M E

namespace HypCGen

variable {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem E_le_H (h : HypCGen G M q E H) : E ≤ H :=
  h.mem.1.2.1

theorem not_le (h : HypCGen G M q E H) : ¬ H ≤ M :=
  h.mem.1.2.2.1

theorem ne_top (h : HypCGen G M q E H) : H ≠ ⊤ :=
  h.mem.1.1

theorem two_le_pRank (h : HypCGen G M q E H) : 2 ≤ CFSG.Open.pRank q E :=
  CFSG.SectionRank.le_pRank h.prime.one_lt le_rfl h.elem h.card

theorem E_ne_bot {q : ℕ} (h : HypCGen G M q E H) : E ≠ ⊥ := by
  intro hbot
  have hc := h.card
  rw [hbot, Subgroup.card_bot] at hc
  exact (Nat.one_lt_pow two_ne_zero h.prime.one_lt).ne hc

theorem isPGroup (h : HypCGen G M q E H) : IsPGroup q E :=
  CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup q E h.elem

theorem isTwoLocal (h : HypCGen G M q E H) : IsTwoLocal H := by
  haveI := h.cstar.simple
  exact isTwoLocal_of_mem_H2StarFam h.cstar.nonab h.cstar.charTwo h.E_ne_bot h.mem

theorem not_mem_sigmaA (h : HypCGen G M q E H) : q ∉ rankThreeSigmaA G := fun hq =>
  h.not_le (h.cstar.embed q hq M h.maxLocal E h.E_le_M h.isPGroup h.two_le_pRank H h.isTwoLocal
    h.E_le_H)

theorem not_mem_sigmaSet (h : HypCGen G M q E H) : q ∉ sigmaSet G M :=
  fun hq => h.not_mem_sigmaA hq.1

theorem mem_QSet (h : HypCGen G M q E H) : E ∈ QSet M q :=
  ⟨h.prime, h.odd, h.E_le_M, h.isPGroup, Or.inr ⟨E, le_rfl, h.elem, h.card, h.gamma⟩⟩

theorem mem_HFam (h : HypCGen G M q E H) : H ∈ HFam M E :=
  ⟨h.ne_top, h.E_le_H, h.not_le⟩

theorem mem_H2Fam (h : HypCGen G M q E H) : H ∈ H2Fam M E :=
  h.mem.1

end HypCGen

theorem kSub_le (p : ℕ) (M H : Subgroup G) : kSub p M H ≤ H := by
  unfold kSub
  split_ifs with h
  · exact sSup_le fun Y hY => hY.1
  · exact sSup_le fun Y hY => hY.1.1

theorem mem_H2StarFam_of_le {M E A H : Subgroup G} (hH : H ∈ H2StarFam M E) (hAH : A ≤ H) :
    H ∈ H2StarFam M A := by
  refine ⟨⟨hH.1.1, hAH, hH.1.2.2.1, hH.1.2.2.2⟩, ?_⟩
  intro H' hH' hHH'
  exact hH.2 H' ⟨hH'.1, hH.1.2.1.trans hHH', hH'.2.2.1, hH'.2.2.2⟩ hHH'

@[expose] def FourteenFifteenOneAt {G : Type} [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H →
    ∃ A : Subgroup G, A ≤ kSub q M H ∧ A ≤ M ∧ CFSG.Open.IsElemAbelian q A ∧
      Nat.card A = q ^ 2 ∧ CFSG.Open.rankThreeGamma 1 q A ≤ M

namespace HypCGen

theorem of_le {M : Subgroup G} {q : ℕ} {E H A : Subgroup G} (h : HypCGen G M q E H)
    (hAH : A ≤ H) (hAM : A ≤ M) (hA : CFSG.Open.IsElemAbelian q A) (hAc : Nat.card A = q ^ 2)
    (hΓ : CFSG.Open.rankThreeGamma 1 q A ≤ M) : HypCGen G M q A H :=
  { cstar := h.cstar
    maxLocal := h.maxLocal
    sigma_nonempty := h.sigma_nonempty
    prime := h.prime
    odd := h.odd
    E_le_M := hAM
    elem := hA
    card := hAc
    gamma := hΓ
    mem := mem_H2StarFam_of_le h.mem hAH }

theorem exists_kSub_maximal {M : Subgroup G} {q : ℕ} {A H : Subgroup G}
    (h : HypCGen G M q A H) (hAK : A ≤ kSub q M H) :
    ∃ H' : Subgroup G, HypCGen G M q A H' ∧ A ≤ kSub q M H' ∧ kSub q M H ≤ kSub q M H' ∧
      ∀ H₁ ∈ H2StarFam M A, kSub q M H' ≤ kSub q M H₁ → kSub q M H₁ = kSub q M H' := by
  classical
  let s : Set (Subgroup G) := {H₁ | H₁ ∈ H2StarFam M A ∧ kSub q M H ≤ kSub q M H₁}
  obtain ⟨K, hKmem, hKmax⟩ := (Set.toFinite (kSub q M '' s)).exists_maximal
    ⟨kSub q M H, H, ⟨h.mem, le_rfl⟩, rfl⟩
  obtain ⟨H', hH's, rfl⟩ := hKmem
  refine ⟨H', { h with mem := hH's.1 }, hAK.trans hH's.2, hH's.2, fun H₁ hH₁ hle => ?_⟩
  exact le_antisymm (hKmax ⟨H₁, ⟨hH₁, hH's.2.trans hle⟩, rfl⟩ hle) hle

end HypCGen

@[expose] def FourteenFifteenTwoAt {G : Type} [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H → E ≤ kSub q M H →
    (∀ H₁ ∈ H2StarFam M E, kSub q M H ≤ kSub q M H₁ → kSub q M H₁ = kSub q M H) →
    ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M) →
      CFSG.ABGLocalTools.IsSylowOf 2 T M ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 T H

theorem exists_hypCGen (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G} (hQM : Q ≤ M) (hQp : IsPGroup q Q)
    (hQ2 : 2 ≤ CFSG.Open.pRank q Q) (hΓ : CFSG.Open.rankThreeGamma 1 q Q ≤ M)
    {H₀ : Subgroup G} (hH₀ : CFSG.Open.IsTwoLocal H₀) (hQH₀ : Q ≤ H₀) (hH₀M : ¬ H₀ ≤ M) :
    ∃ E H : Subgroup G, E ≤ Q ∧ HypCGen G M q E H ∧
      ∀ H₁ ∈ H2StarFam M E, kSub q M H ≤ kSub q M H₁ → kSub q M H₁ = kSub q M H := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hC.simple
  obtain ⟨E, hEQ, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (k := 2) hQ2
  have hEM : E ≤ M := hEQ.trans hQM
  have hΓE : rankThreeGamma 1 q E ≤ M := by
    refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 q E M).mpr fun R hRE hR => ?_
    exact (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q Q R
      (hRE.trans hEQ) hR).trans hΓ
  have hEH₀ : E ≤ H₀ := hEQ.trans hQH₀
  have hH₀mem : H₀ ∈ H2Fam M E :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab H₀ hH₀, hEH₀, hH₀M,
      hC.charTwo H₀ hH₀⟩
  obtain ⟨H₂, hH₂star, -⟩ := exists_mem_H2StarFam_le hH₀mem
  obtain ⟨K, hKmem, hKmax⟩ := (Set.toFinite (kSub q M '' H2StarFam M E)).exists_maximal
    ⟨kSub q M H₂, H₂, hH₂star, rfl⟩
  obtain ⟨H, hHstar, rfl⟩ := hKmem
  refine ⟨E, H, hEQ, ⟨hC, hM, hσ, hq, hq2, hEM, hE, hEc, hΓE, hHstar⟩,
    fun H₁ hH₁ hle => ?_⟩
  exact le_antisymm (hKmax ⟨H₁, hH₁, rfl⟩ hle) hle

theorem fourteenFifteenAt_of_one_two (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (h1 : FourteenFifteenOneAt M) (h2 : FourteenFifteenTwoAt M) : FourteenFifteenAt M := by
  intro q hq hq2 _ Q hQM hQp hQ2 hΓ H₀ hH₀ hQH₀ hH₀M S hSM
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, H, -, hdata, -⟩ :=
    exists_hypCGen (G := G) hC hM hσ hq hq2 hQM hQp hQ2 hΓ hH₀ hQH₀ hH₀M
  obtain ⟨A, hAK, hAM, hA, hAc, hΓA⟩ := h1 q E H hdata
  have hAH : A ≤ H := hAK.trans (kSub_le q M H)
  have hdataA : HypCGen G M q A H := HypCGen.of_le hdata hAH hAM hA hAc hΓA
  obtain ⟨H', hdata', hAK', -, hmax'⟩ := HypCGen.exists_kSub_maximal hdataA hAK
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H' ⊓ M)
  obtain ⟨hTM, hTH⟩ := h2 q A H' hdata' hAK' hmax' T hT
  have hStopsyl : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  have hSMsyl : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup G) M :=
    hStopsyl.of_le hSM le_top
  have hTtop : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hTM.card_eq, ← hSMsyl.card_eq, hStopsyl.card_eq]
  exact hTH (hTtop.of_le (hT.le.trans inf_le_left) le_top)

theorem agl81FourteenFifteen_of_one_two
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        FourteenFifteenOneAt M ∧ FourteenFifteenTwoAt M) :
    AGL81FourteenFifteen := by
  intro G _ _ hC M hM hσ
  obtain ⟨h1, h2⟩ := h G hC M hM hσ
  exact fourteenFifteenAt_of_one_two hC hM hσ h1 h2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
