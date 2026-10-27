module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactParabolicWCent
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Assembly.InCatalog
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourYCentJ
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourYCentL
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourBlockRank
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockExists
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJLeX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourASevenLeX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJLeXSpor
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourStepA
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourExistsWitness
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourCentW
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourCentWASeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourNormW
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourFinalCaseSixSpor
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourFinalCaseTwo
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockOrderThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicHolds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutModels
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrime
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusLin
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerTorusUni
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumComponent
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.Quasithin.Background.C126Split2
import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
import CFSG.RankThree.PartOne.S11c.Sec66E6
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.SteinbergR3ECAFieldFixedLayerQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem stepA_of_twelveThreeData (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) {L : Subgroup G} (hBL : TwelveFourBlockFacts M H L)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) (hL : L ∈ weakBlockSet M H)
    (hD : ∀ d ∈ sigmaSet G M, d ∣ Nat.card (H ⊓ M : Subgroup G) → TwelveThreeData M p H d) :
    TwelveFourStepA M d := by
  refine twelveFourStepA_of_blocks h hd hBL ?_
  intro h3m
  have h3dvdHM : 3 ∣ Nat.card (H ⊓ M : Subgroup G) := by
    have hle : L ⊓ H ≤ H ⊓ M := by
      intro x hx
      exact ⟨hx.2, hL.le hx.1⟩
    exact dvd_trans hBL.three_dvd (Subgroup.card_dvd_of_le hle)
  have hD3 := hD 3 h3m h3dvdHM
  have hc : TwelveThreeCaseTwo M p H 3 ∨ TwelveThreeCaseSix M p H 3 := by
    rcases hD3.cases with c2 | c6 | cspor
    · exact Or.inl c2
    · exact Or.inr c6
    · exact absurd rfl (TwelveThreeCaseSpor.ne_three cspor)
  exact ⟨hD3.common.xSub_dPrime, jOne_le_xSub_of_caseTwo_or_caseSix h hsyl h3m hc hL,
    twelveFourASevenLeX_of_caseTwo_or_caseSix h hsyl h3m hc hL hBL⟩

private theorem jLeX_of_twelveThreeData (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) (hD' : TwelveThreeData M p H d) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hJS : ∀ d : ℕ, TwelveThreeData M p H d → TwelveThreeCaseSpor M p H d →
      ∀ L ∈ weakBlockSet M H, jOne H L ≤ xSub p M H) :
    jOne H L ≤ xSub p M H := by
  rcases hD'.cases with h2 | h6 | hspor
  · exact jOne_le_xSub_of_caseTwo_or_caseSix h hsyl hd (Or.inl h2) hL
  · exact jOne_le_xSub_of_caseTwo_or_caseSix h hsyl hd (Or.inr h6) hL
  · exact hJS d hD' hspor L hL

private theorem aSevenLeX_of_twelveThreeData (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) (hD' : TwelveThreeData M p H d) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (hBL : TwelveFourBlockFacts M H L)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    TwelveFourASevenLeX M p H L := by
  rcases hD'.cases with h2 | h6 | hspor
  · exact twelveFourASevenLeX_of_caseTwo_or_caseSix h hsyl hd (Or.inl h2) hL hBL
  · exact twelveFourASevenLeX_of_caseTwo_or_caseSix h hsyl hd (Or.inr h6) hL hBL
  · exact twelveFourASevenLeX_of_caseSpor h hD' hspor hL hBL

private theorem witness_of_twelveThreeData
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hK5 : KFactOddAutParabolicFixPrime)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    (h : TwelveCtx G M p Q H) {d : ℕ} (hd : d ∈ sigmaSet G M)
    {L : Subgroup G} (hBL : TwelveFourBlockFacts M H L)
    (hL : L ∈ weakBlockSet M H) (hA : TwelveFourStepA M d) (hYL : TwelveFourYCentL M H L d)
    (hJX : jOne H L ≤ xSub p M H) (hA7 : TwelveFourASevenLeX M p H L)
    (hR : TwelveFourBlockRank M H L d) :
    ∃ W : Subgroup G, TwelveFourWitness M p H d W := by
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hJ : ¬ NineThreeFive M L → ∀ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 S (jOne H L) →
        2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (S : Set G)) := by
    intro _ S hS
    have hphase : CFSG.AGLEmbedding.TwoLocalPhaseThree M H := h.twoLocalPhaseThree
    have hK : CFSG.Open.IsKGroup ↥M :=
      CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
        (@CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top G _ _ h.cstar.simple
          h.cstar.nonab M h.maxLocal.1)
    have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
      noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
    have hSyl : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
      hphase.not_isSylowTwoOf_inf hK h85 hD2 hL
    have hNine : NineThreeConclusion M (pCoreOf 2 H) L :=
      hphase.nineThree hK h93 hL
    have hn1 : ¬ NineThreeOne L := (hphase.nineThree_not_one hK h85 hD2 hL).1
    exact two_le_pRank_inf_centralizer_of_isSylowOf_jOne_of_kFacts hN1 hK5 hOut hT h hA.2.1
      hd hA.2.2 hL hBL.order_three hSyl hNine hn1 hYL.1 hR.1 hS
  have h7' : NineThreeFive M L → ∀ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 S (H ⊓ L) →
        2 ≤ CFSG.Open.pRank d (M ⊓ Subgroup.centralizer (S : Set G)) := by
    intro h5 S hS
    exact two_le_pRank_inf_centralizer_of_nineThreeFive h hA.2.1 hd hA.2.2 hL h5 hS
  exact exists_twelveFourWitness hdp hL hBL hYL hJX hA7 hJ h7'

theorem twelveFourOne_of_twelveThreeData
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hI : NineNineOneInput)
    (hKer : NineTwelveKerGen) (hO812 : Section15.O812sixGen)
    (hWc : KFactParabolicWCentSolvable) (hS : SchreierFor InCatalog)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hK5 : KFactOddAutParabolicFixPrime)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    (h : TwelveCtx G M p Q H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hB : ∀ L ∈ weakBlockSet M H, TwelveFourBlockFacts M H L)
    (h33 : ∀ L ∈ weakBlockSet M H, CFSG.Open.pRank 3 M ≤ 3 → TwelveFourTenThreeThree M H L)
    (hJS : ∀ d : ℕ, TwelveThreeData M p H d → TwelveThreeCaseSpor M p H d →
      ∀ L ∈ weakBlockSet M H, jOne H L ≤ xSub p M H)
    (hD : ∀ d ∈ sigmaSet G M, d ∣ Nat.card (H ⊓ M : Subgroup G) → TwelveThreeData M p H d) :
    ∀ d ∈ sigmaSet G M, ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := by
  intro d hd hdH
  have hD' : TwelveThreeData M p H d := hD d hd hdH
  obtain ⟨L, hL⟩ := weakBlockSet_nonempty h1 h2 h25 h84 h
  have hBL : TwelveFourBlockFacts M H L := hB L hL
  have hA : TwelveFourStepA M d := stepA_of_twelveThreeData h hd hBL hsyl hL hD
  have hJX : jOne H L ≤ xSub p M H := jLeX_of_twelveThreeData h hd hD' hL hsyl hJS
  have hA7 : TwelveFourASevenLeX M p H L := aSevenLeX_of_twelveThreeData h hd hD' hL hBL hsyl
  have hYJ : TwelveFourYCentJ M H L d := twelveFourYCentJ_of_twelveCtx hS h hd hD' hA hL hBL hJX
  have hYL : TwelveFourYCentL M H L d :=
    twelveFourYCentL_of_twelveCtx hWc h hd hD' hA hL hBL (h33 L hL hA.2.1) hYJ
  have hR : TwelveFourBlockRank M H L d := twelveFourBlockRank_of_twelveCtx h hd hD' hA hL hYL
  obtain ⟨W, hW⟩ := witness_of_twelveThreeData h1 h2 h25 h85 h93 hN1 hK5 hOut hT h hd hBL hL
    hA hYL hJX hA7 hR
  have hN := normalizer_le_of_twelveFourWitness hO812 h hd hD' hA hL hW
  rcases hD'.cases with c2 | c6 | cs
  · exact false_of_twelveFour_caseTwo hKer hI h hd hA c2 hW.1 hW.2.1 hN
  · exact false_of_twelveFour_caseSixSpor hKer hI h hD' (Or.inl c6) hW.1 hW.2.1 hN
  · exact false_of_twelveFour_caseSixSpor hKer hI h hD' (Or.inr cs) hW.1 hW.2.1 hN

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
