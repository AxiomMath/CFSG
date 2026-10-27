module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual7
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
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
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Structure312Defs
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
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def U4ShapeAt (n p : ℕ) (M : Subgroup G) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = n ∧ d.1 = .twistedA 3 q ∧
      p ∣ q.card + 1) ∧
    Nonempty ((↥(CFSG.RankThree.PartOne.pElementSubgroup p M) ⧸
      CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup p M)) ≃*
        (TauCeti.CFSGIndex.lie d).Group)

theorem U4Shape.exists_shapeAt {p : ℕ} {M : Subgroup G} (h : U4Shape p M) :
    ∃ n, U4ShapeAt n p M := by
  obtain ⟨d, ⟨q, hq2, hd, hpq⟩, he⟩ := h
  exact ⟨q.exponent, d, ⟨q, hq2, rfl, hd, hpq⟩, he⟩

@[expose] def NaturalU4ModuleConclusion (n : ℕ) (L V : Subgroup G) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ (ε : ↥L →* ↥(StatedSU 4 (2 ^ n) F)) (φ : ↥⁅V, L⁆ →* Multiplicative (Fin 4 → F)),
      Function.Surjective ε ∧ Function.Surjective φ ∧ ε.ker = CFSG.pCore 2 ↥L ∧
      φ.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆ ∧
      ∀ (l : ↥L) (u u' : ↥⁅V, L⁆), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
        φ u' = Multiplicative.ofAdd
          (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (φ u)))) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥L →* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (φ : ↥⁅V, L⁆ →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      Function.Surjective ε ∧ Function.Surjective φ ∧ ε.ker = CFSG.pCore 2 ↥L ∧
      φ.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆ ∧
      ∀ (l : ↥L) (u u' : ↥⁅V, L⁆), (l : G) * (u : G) * (l : G)⁻¹ = (u' : G) →
        φ u' = Multiplicative.ofAdd
          (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (φ u))))

@[expose] def KFactAGL81I54U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p n : ℕ) (M T : Subgroup G), p.Prime → p ≠ 2 →
    M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M →
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
    U4ShapeAt n p M →
    ¬ CFSG.RankThree.PartOne.pElementSubgroup p M ≤ centralizer (uCore M T : Set G) →
    2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) →
    NaturalU4ModuleConclusion n (CFSG.RankThree.PartOne.pElementSubgroup p M) (uCore M T)

end CFSG.LocalAnalysis.RankThreeUC
