module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenClauses
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenPClosed
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
public import CFSG.RankThree.PartTwo.Sec5.Hyp
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
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
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

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

@[expose] def NineNineOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → p ∉ sigmaM G M → NineNineOne M p

@[expose] def NineSixTwoComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → ¬ pLayerIn p H ≤ M →
      {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M}.ncard ≤ 2

@[expose] def NineSixThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 3 Q H E 2 → H ∈ H2Fam M Q → 3 ∉ sigmaM G M → ¬ pLayerIn 3 H ≤ M →
    CFSG.IsQuasisimple ↥(kStar 3 M H) →
    (CFSG.Open.pRank 3 (kStar 3 M H) = 1 ∨
      (CFSG.Open.pRank 3 (kStar 3 M H) = 2 ∧ center ↥(kStar 3 M H) ≠ ⊥)) →
    IsPSLType 2 (GaloisField 2 3) ↥(kStar 3 M H) ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
        (fun B _ => Nat.card B = 3) ↥(kStar 3 M H) ∨
      IsSLType 3 (GaloisField 2 2) ↥(kStar 3 M H)

@[expose] def NineTenFivePClosed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 5 Q H E 2 → H ∈ H2Fam M Q → 5 ∉ sigmaM G M →
    ∀ C : Subgroup (StarGroup 5 H), CFSG.IsComponent C →
      IsPClosedMod 5 ((C ⊔ centralizer (C : Set (StarGroup 5 H))).subgroupOf
        (normalizer (C : Set (StarGroup 5 H))))

@[expose] def KFactCenterRankTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ L : Subgroup X,
    CFSG.IsComponent L → ∀ p : ℕ, p.Prime → p ≠ 2 → 2 ≤ CFSG.Open.pRank p (center ↥L) →
      4 ≤ CFSG.Open.pRank p L

@[expose] def SixSixOneRank : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X], p.Prime → 3 < p →
    closure {x : X | orderOf x = p} = ⊤ →
    centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X → CFSG.pCore p X ≠ ⊤ →
    CFSG.RankThree.PartTwo.IsSymplecticType ↥(CFSG.pCore p X) →
    CFSG.Open.pRank p (CFSG.pCore p X) = 2 →
      CFSG.Open.pRank p (⊤ : Subgroup X) = 3

structure SevenOneUsed : Prop where
  three : SevenOneThree
  twoOne : KFactOmegaNotCentral

@[expose] def KFactThreeFiveRankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore 3 X = ⊥ →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
    ∀ K E : Subgroup X, CFSG.IsComponent K → CFSG.Open.pRank 3 K = 1 →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → E ≤ Subgroup.normalizer (K : Set X) →
      ¬ K ≤ CFSG.Open.rankThreeGamma 1 3 E →
      IsPSLType 2 (GaloisField 2 3) ↥K

structure NineTenInputs : Prop where
  sevenOne : SevenOneUsed
  nineTenPClosed : ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → 3 < p →
    ∀ C : Subgroup (StarGroup p H), CFSG.IsComponent C →
      (h3C : 2 ≤ CFSG.Open.pRank 3 C) →
      IsPClosedMod p ((C ⊔ centralizer (C : Set (StarGroup p H))).subgroupOf
        (normalizer (C : Set (StarGroup p H))))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
