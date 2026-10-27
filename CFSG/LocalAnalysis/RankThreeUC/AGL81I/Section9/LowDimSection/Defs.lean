module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSolv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
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
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
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

open Subgroup CFSG.LocalAnalysis.RankThreeUC.S15 MatrixGroups

@[expose] def IsLowDimSimpleSection (q : ℕ) [Fact q.Prime] (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* PSL(2, ZMod q)) ∨ Nonempty (S ≃* PSL(3, ZMod q)) ∨
    Nonempty (S ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q))) ∨
    Nonempty (S ≃* PSL(2, GaloisField q 2)) ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (S ≃* GL (Fin 3) (ZMod 2))

@[expose] def LowDimMulAutSection : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
    ∀ (V : Type) [Group V] [Finite V], IsPGroup q V → CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3 →
    ∀ (A : Subgroup (MulAut V)) (S : Type) [Group S] [IsSimpleGroup S], ¬ IsMulCommutative S →
    ∀ φ : ↥A →* S, Function.Surjective φ → IsLowDimSimpleSection q S

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
