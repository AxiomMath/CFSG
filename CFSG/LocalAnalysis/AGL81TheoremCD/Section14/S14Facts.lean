module

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactA9NotInvolvedGL4Holds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactL34FixedPointsProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaU3
import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFalse
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFalse
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

structure S14FactsAt (M : Subgroup G) : Prop where
  pre : PreambleTypes M
  three : ∀ H ∈ H2StarAll M, CaseThree M H
  two : KTwoComponentAt M
  normal : KNormalAt M
  layer : PLayerNotLeAt M
  nine : NineNineOneAt M
  inner : InnerOnKAt M

@[expose] def S14FactsGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → S14FactsAt M

private theorem preamble_nine_layer
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen) (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hC : CStarGen G) {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty) :
    PreambleTypes M ∧ NineNineOneAt M ∧ PLayerNotLeAt M := by
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 hC hM hσ (preambleFiveTypes_of h1210 h97 h96 hC hM hσ hU)
  exact ⟨hpre, hU, pLayerNotLeAt_of h1211 h1210 h97 hU⟩

theorem s14FactsGen_of_caseOne
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) (hinv : KFactL34NotInvolvedA11)
    (hC1 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → CaseOneFalse M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (h73 : SevenThreeInput) (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hX : ∀ (G : Type) [Group G] [Finite G], CStarGen G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h1453 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFiveThreeAt M) :
    S14FactsGen := by
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hU, hL⟩ := preamble_nine_layer h1210 h1211 h97 h96 h991 hC hM hσ
  have hch : ChoiceExists M :=
    choiceExists_of hC hM hσ h1211 hpre hU hL hS hinv
  have h2 : CaseTwoFalse M :=
    caseTwoFalse_of hpre hU hL hKF h514 h525 (hX G hC) h73 h711
      (h1453 G hC M hM hσ) kFactA9NotInvolvedGL4_holds
  have h14 : ∀ H ∈ H2StarAll M, CaseThree M H :=
    caseThree_of_cases hpre hch (hC1 G hC M hM hσ) h2
  have hTwo : KTwoComponentAt M := kTwoComponentAt_of hS h14 hL
  have hK : KNormalAt M := kNormalAt_of_preamble hpre hU hL
  exact ⟨hpre, h14, hTwo, hK, hL, hU, innerOnKAt_of hK hL kFactL34FixedPointsGen⟩

theorem s14FactsGen_of_caseOneInputs
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) (hinv : KFactL34NotInvolvedA11)
    (h142 : FourteenTwoCaseOneGen) (h143 : FourteenThreeCaseOneGen)
    (h145 : FourteenFiveCaseOneGen)
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145)
    (h1410 : KFact1410a) (h4143 : K4143NoExtraspecial)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (h73 : SevenThreeInput) (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hX : ∀ (G : Type) [Group G] [Finite G], CStarGen G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h1453 : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFiveThreeAt M) :
    S14FactsGen :=
  s14FactsGen_of_caseOne h1210 h1211 h97 h96 hS h991 hinv
    (caseOneFalse_gen h142 h143 h145 hFF h7145 h1410 h4143 (by
      intro G _ _ hC M hM hσ
      exact preamble_nine_layer h1210 h1211 h97 h96 h991 hC hM hσ))
    hKF h514 h525 h73 h711 hX h1453

theorem mem_H2StarFam_of_isMaxTwoLocal_of_ne (hC : CStarGen G) {M E H : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hE : E ≠ ⊥)
    (hH : CFSG.Open.rankThreeIsMaxTwoLocal H) (hEH : E ≤ H) (hHM : H ≠ M) :
    H ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.H2StarFam M E := by
  haveI := hC.simple
  have hHmem : H ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.H2Fam M E :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab H hH.1, hEH,
      fun hle => hHM (hH.2 M hM.1 hle).symm, hC.charTwo H hH.1⟩
  refine ⟨hHmem, fun N' hN' hHN' => ?_⟩
  have hO2ne : CFSG.Open.pCoreOf 2 N' ≠ ⊥ := by
    intro hbot
    have hcharN' := hN'.2.2.2
    rw [hbot] at hcharN'
    have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      have hx1 : x = 1 := by simpa using hx
      simp [hx1]
    rw [htop, inf_top_eq] at hcharN'
    exact hE (le_bot_iff.mp (hN'.2.1.trans hcharN'))
  have hloc : IsTwoLocal (Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 N', hO2ne,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N', rfl⟩
  have hNle : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G) :=
    hHN'.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N')
  have heq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 N' : Set G) = H :=
    hH.2 _ hloc hNle
  exact le_antisymm
    ((CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N').trans
      heq.le) hHN'

theorem hypCGen_of_isMaxTwoLocal (hC : CStarGen G) {M E H : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (hEM : E ≤ M) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ M) (hH : CFSG.Open.rankThreeIsMaxTwoLocal H)
    (hEH : E ≤ H) (hHM : H ≠ M) : HypCGen G M 3 E H := by
  have hEbot : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  exact
    { cstar := hC
      maxLocal := hM
      sigma_nonempty := hσ
      prime := Nat.prime_three
      odd := by norm_num
      E_le_M := hEM
      elem := hE
      card := by rw [hEc]; norm_num
      gamma := hΓ
      mem := mem_H2StarFam_of_isMaxTwoLocal_of_ne hC hM hEbot hH hEH hHM }

theorem S14FactsAt.normalizerSylowKLe
    {M : Subgroup G} (hF : S14FactsAt M) :
    NormalizerSylowKLeAt M :=
  normalizerSylowKLeAt_of hF.pre hF.three hF.normal hF.nine hF.inner

theorem S14FactsAt.kSubLe
    {M : Subgroup G} (hF : S14FactsAt M) : KSubLeKSubAt M :=
  kSubLeKSubAt_of hF.three hF.two hF.normal

theorem S14FactsAt.twoAt
    {M : Subgroup G} (hF : S14FactsAt M) : FourteenFifteenTwoAt M :=
  fourteenFifteenTwoAt_of
    (fourteenFifteenNormAt_of hF.pre hF.three hF.two hF.normal hF.layer) hF.normal
    (kSylowTwoNotLeAt_of hF.pre hF.three hF.normal hF.layer hF.normalizerSylowKLe)

theorem S14FactsAt.exists_l34Data
    {M E H : Subgroup G} (hF : S14FactsAt M)
    (h : HypCGen G M 3 E H) :
    ∃ A H' : Subgroup G, HypCGen G M 3 A H' ∧ A ≤ kSub 3 M H' ∧
      (∀ H₁ ∈ H2StarFam M A, kSub 3 M H' ≤ kSub 3 M H₁ →
        kSub 3 M H₁ = kSub 3 M H') ∧
      CaseThree M H' ∧ Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H' ≤ M := by
  obtain ⟨A, hAK, hAM, hAelem, hAcard, hAΓ⟩ :=
    fourteenFifteenOneAt_of hF.pre hF.three hF.normal hF.nine hF.inner 3 E H h
  have hAH : A ≤ H := hAK.trans (kSub_le 3 M H)
  have hdataA : HypCGen G M 3 A H := HypCGen.of_le h hAH hAM hAelem hAcard hAΓ
  obtain ⟨H', hdata', hAK', -, hmax'⟩ := HypCGen.exists_kSub_maximal hdataA hAK
  have hC3' : CaseThree M H' := hF.three H' hdata'.mem_H2StarAll
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAHM : A ≤ H' ⊓ M :=
    le_inf (hAK'.trans (kSub_le 3 M H')) hAM
  obtain ⟨P, hP, hAP⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge hAHM hdata'.isPGroup
  have hU3 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOne M 3 := hF.nine 3 A H' hdata'
  obtain ⟨hAsyl, -, hAinf_card, hNA, -⟩ :=
    HypCGen.fourteenFifteen_steps hdata' hC3' hF.normal hU3 hF.inner hP hAP
  have hAcard9 : Nat.card A = 9 := by rw [hAcard]; norm_num
  have hcardA : Nat.card A = Nat.card ((P ⊓ kSub 3 M H' : Subgroup G)) := by
    rw [hAcard9, hAinf_card]
  have hAinf : A ≤ P ⊓ kSub 3 M H' := le_inf hAP hAK'
  have hAeq : A = P ⊓ kSub 3 M H' :=
    Subgroup.eq_of_le_of_card_ge hAinf (le_of_eq hcardA.symm)
  refine ⟨A, H', hdata', hAK', hmax', hC3', ?_⟩
  rw [hAeq]
  exact hNA

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
