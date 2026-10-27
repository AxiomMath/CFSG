module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1219Sigma
import all CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1219Sigma
public import Certificates.Kernel.ThCent.Leaves
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
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
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

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.RankThreeUC.S15.O1219SigmaProof

@[expose] def O1217SigmaAt (G : Type) [Group G] [Finite G] (M : Subgroup G) : Prop :=
  ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
      q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) →
      (∀ A : Subgroup G, A ≤ E → Nat.card A = p →
        2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G))) →
      rankThreeGamma 1 p E ≤ M

@[expose] def O1217SigmaGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      (∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      O1217SigmaAt G M

theorem O1217SigmaAt.toO1217At {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (h : O1217SigmaAt G M) : Section15.O1217At G M :=
  fun q p hq _ hp hp2 E hEM hE hEc hqC hrk => h q p hq hp hp2 E hEM hE hEc hqC hrk

theorem o1217Gen_of_o1217SigmaGen (h : O1217SigmaGen) : Section15.O1217Gen :=
  fun G _ _ hC M hM hne hst => (h G hC M hM hne hst).toO1217At

theorem O1217SigmaAt.toO1219SigmaAt {G : Type} [Group G] [Finite G] (hC : CStarGen G)
    {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h : O1217SigmaAt G M) :
    Section15.O1219SigmaAt G M := by
  intro q p hq hp hp2 hpσ D hDM hDnc hDexp _ hrk
  have hqq : q.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1
  have hqp : q ≠ p := fun hqp => hpσ (hqp ▸ hq)
  have h3 : 3 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (D : Set G)) := by
    rw [hrk]
    exact hC.three_le_pRank_of_mem_sigmaSet hM hq
  obtain ⟨F, hFle, hF, hFc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hqq h3
  have hFM : F ≤ M := hFle.trans inf_le_left
  have hFD : F ≤ Subgroup.normalizer (D : Set G) := hFle.trans inf_le_right
  obtain ⟨E, hED, hEabel, hEcard, hqC, hA⟩ := key_good hqq hp hqp hF hFc hFD hDexp hDnc
  refine ⟨E, hED, hEabel, hEcard, ?_⟩
  refine h q p hq hp hp2 E (hED.trans hDM) hEabel hEcard ?_ ?_
  · exact dvd_trans hqC (Subgroup.card_dvd_of_le (inf_le_inf_right _ hFM))
  · intro A hAE hAc
    obtain ⟨K, hKle, hKe, hKc⟩ := hA A hAE hAc
    exact CFSG.SectionRank.le_pRank hqq.one_lt (hKle.trans (inf_le_inf_right _ hFM)) hKe hKc

theorem o1219SigmaGen_of_o1217SigmaGen (h : O1217SigmaGen) : Section15.O1219SigmaGen :=
  fun G _ _ hC M hM hne hst => (h G hC M hM hne hst).toO1219SigmaAt hC hM

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
