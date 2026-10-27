module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Foundations.Basic
public import CFSG.RankThree.SubgroupLists.SchurCommutant
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
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
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

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

@[expose] def IsCommutatorModel (p : ℕ) {X W : Type*} [Group X] [AddCommGroup W]
    [Module (ZMod p) W] (φ : X →* (Module.End (ZMod p) W)ˣ)
    (B : LinearMap.BilinForm (ZMod p) W) : Prop :=
  ∃ (D Z : Subgroup X) (bar : X → W), D.Normal ∧ Z ≤ D ∧ Nat.card Z = p ∧
    (∀ d ∈ D, d ^ p = 1) ∧ (∀ a ∈ D, ∀ b ∈ D, bar (a * b) = bar a + bar b) ∧
    (∀ d ∈ D, bar d = 0 ↔ d ∈ Z) ∧ (∀ w : W, ∃ d ∈ D, bar d = w) ∧
    (∀ x : X, ∀ d ∈ D, bar (x * d * x⁻¹) = (φ x : Module.End (ZMod p) W) (bar d)) ∧
    (∀ a ∈ D, ∀ b ∈ D, B (bar a) (bar b) = 0 → a * b = b * a) ∧
    ∀ x : X, (∀ u v : W, B ((φ x : Module.End (ZMod p) W) u)
      ((φ x : Module.End (ZMod p) W) v) = B u v) → ∀ c ∈ Z, x * c = c * x

@[expose] def HasIsotropicPlaneGroup (p : ℕ) {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (B : LinearMap.BilinForm (ZMod p) W) (H : Subgroup (Module.End (ZMod p) W)ˣ) : Prop :=
  -1 ∈ H ∧ ∃ E : Subgroup (Module.End (ZMod p) W)ˣ, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
    Nat.card E = p ^ 2 ∧ ∃ π : Submodule (ZMod p) W, Module.finrank (ZMod p) π = 2 ∧
      (∀ u ∈ π, ∀ v ∈ π, B u v = 0) ∧ ∀ e ∈ E, ∀ u ∈ π, (e : Module.End (ZMod p) W) u = u

@[expose] def SympSplitAt (p : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W],
    Module.finrank (ZMod p) W = 4 → ∀ B : LinearMap.BilinForm (ZMod p) W,
    (∀ u : W, (∀ v : W, B u v = 0) → u = 0) → (∀ w : W, B w w = 0) →
    ∀ H : Subgroup (Module.End (ZMod p) W)ˣ, oPPrimeHull p H = H →
      (∀ x ∈ H, ∃ c : ZMod p, ∀ u v : W,
        B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = c * B u v) →
      SixThreeOneList p (↥H ⧸ CFSG.pCore p ↥H) ∨ HasIsotropicPlaneGroup p B H

@[expose] def SympIrredNotQuasisimpleAt (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → ∀ G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p)), G ≤ CFSG.Open.StatedSp 2 (ZMod p) →
    oPPrimeHull p G = G → CFSG.RankThree.SubgroupLists.IsIrreducibleOn G →
      ¬ CFSG.IsQuasisimple ↥G →
      p = 5 ∧ (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
          (fun B _ => IsQ8D8Type B) ↥G ∨
        IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) ↥G)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
