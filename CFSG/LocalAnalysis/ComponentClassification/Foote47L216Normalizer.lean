module

import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom
import CFSG.GroupTheory.InvolutionConjParity
import CFSG.GroupTheory.OddIndexThreeInvolution
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
public import CFSG.Monster.Existence.StdOdd.Cert.ThreeLocalLemmas
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMLift
public import CFSG.GroupTheory.Frattini.MapSubtypeLe
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormSimilarity
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.Foundations.MaxOrderThompsonImage
public import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure

public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216T64
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bAction
public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216AbelianKernel
import CFSG.LocalAnalysis.SteinbergCDCentralTwoExtensionSquare
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec26
import CFSG.Mathlib.GroupTheory.NormalFifteenQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LStruct
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Simple
import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm12KStar
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Transport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216FrobeniusConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBShell
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
import CFSG.LocalAnalysis.ComponentClassification.CTUMirrorL34
import CFSG.LocalAnalysis.ComponentClassification.FooteLitSolomonFamily
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bZStar
import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
import CFSG.LocalAnalysis.ComponentClassification.FooteProperFixedA7
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayerNormalizer
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentralProd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole
import CFSG.LocalAnalysis.ComponentClassification.OddKernel
import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.HSDihedralAssembly
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.Quasithin.EmptyFaithful.S152SProd
import CFSG.LocalAnalysis.ComponentClassification.SolMaxMaximality
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldCentralizer
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.Walter.Bender1970.S2.Involutions
import CFSG.Walter.JRFacts
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
import CFSG.LocalAnalysis.ComponentClassification.Sol76AltClass
import CFSG.GH74.GLS.Statements
import CFSG.GH74.SmallRanks
import CFSG.GH74.KGroups.PSL2
import CFSG.RankThree.OddKernel.TwoRankTwo
public import CFSG.RankThree.OddKernel.OddLift
import CFSG.ClassicalInvolution.TwoGroupCase.TightEmbedding
import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.LocalAnalysis.ComponentClassification.Foote47TwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P2
import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneLayer
import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Act
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Basic
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L54
import CFSG.LocalAnalysis.ComponentClassification.Foote5L511G
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.CentralizerSup
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bConj
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Basic
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Setup
import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.CGT.M24S.Defs
public import CFSG.CGT.T75P.Inputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldConjugacy
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.Certificates.WordSubgroupHom
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Generic.Front.Final
import CFSG.GH74.Generic.FrontEnd
import CFSG.GH74.Generic.S1.LinFull
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentral
import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMaxWeak
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RMain
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36MType
import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools
import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCA7
import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
import CFSG.LocalAnalysis.ComponentClassification.Sol78Pump
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.SeitzReduction.RankOneKernel
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.Quasithin.Background.A1cA132Action
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C2A3Orbits
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Sixteen
import CFSG.Quasithin.Background.InternalSecData
import CFSG.Quasithin.Background.InternalSecIso
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S152FinCore
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.EmptyFaithful.T1515cE
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts04
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Co2Schreier.ModelSimple
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.LyFixedSet
import CFSG.Sporadic.SmallOddCore.Co3Catalogue
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
import CFSG.Sporadic.SuzOddCore.SmallActionData
import CFSG.Sporadic.ThSchreier.ThSchreierCase
import CFSG.StronglyEmbedded.MatrixGroups.PSL2
import CFSG.Walter.W67.W2Lemma26A
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate10025
import Certificates.Certificate10027
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate10115
import Certificates.Certificate10115Base
import Certificates.Certificate10116
import Certificates.Certificate10116Base
import Certificates.Certificate10117
import Certificates.Certificate10117Base
import Certificates.Certificate10118
import Certificates.Certificate10118Base
import Certificates.Certificate10119
import Certificates.Certificate10119Base
import Certificates.Certificate10123
import Certificates.Certificate10123Base
import Certificates.Certificate14953
import Certificates.Certificate16018
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2246
import Certificates.Certificate2323
import Certificates.Certificate5133
import Certificates.Certificate6006
import Certificates.Certificate8171
import Certificates.Certificate9124
import Certificates.Kernel.J4Count.FixC
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

public section
public section
public section
public section
public section
public section
public section
public section
namespace CFSG.ComponentClassification.Foote47L216

open CFSG CFSG.ScalarGraphAction
open scoped Pointwise

noncomputable section

variable {G : Type} [Group G] [Finite G]
variable {W R P : Subgroup G}
variable (hW : W = R ⊔ P)
variable (hRW : R ≤ W) (hPW : P ≤ W)
variable (hPcard : Nat.card P = 4)
variable (eR : R ≃* Multiplicative (GaloisField 2 4))
variable (eW : W ≃* (Multiplicative (GaloisField 2 4) × P))
variable (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
variable (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
variable (φ : P →* Multiplicative (GaloisField 2 4))
variable (hφ : Function.Injective φ)
variable (F : Set (Subgroup W))
variable (hF : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ a : GaloisField 2 4,
    Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
variable (hForbit : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ n : Subgroup.normalizer (W : Set G),
    Q = (W.normalizerMonoidHom n) • P.subgroupOf W)
variable (hNR : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (R : Set G))

local notation "RootField" => GaloisField 2 4

local notation "Norm" => Subgroup.normalizer (W : Set G)

local notation "phiAdd" => MonoidHom.toAdditiveLeft φ

end

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216

open CFSG CFSG.ScalarGraphAction
open scoped Pointwise

noncomputable section

variable {G : Type} [Group G] [Finite G]
variable {W R P : Subgroup G}
variable (hW : W = R ⊔ P)
variable (hRW : R ≤ W) (hPW : P ≤ W)
variable (hPcard : Nat.card P = 4)
variable (eR : R ≃* Multiplicative (GaloisField 2 4))
variable (eW : W ≃* (Multiplicative (GaloisField 2 4) × P))
variable (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
variable (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
variable (φ : P →* Multiplicative (GaloisField 2 4))
variable (hφ : Function.Injective φ)
variable (F : Set (Subgroup W))
variable (hF : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ a : GaloisField 2 4,
    Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
variable (hForbit : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ n : Subgroup.normalizer (W : Set G),
    Q = (W.normalizerMonoidHom n) • P.subgroupOf W)
variable (hNR : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (R : Set G))

local notation "F4" => GaloisField 2 4

local notation "Norm" => Subgroup.normalizer (W : Set G)

end

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216

open CFSG CFSG.ScalarGraphAction
open scoped Pointwise

noncomputable section

variable {G : Type} [Group G] [Finite G]
variable {W R P : Subgroup G}
variable (hW : W = R ⊔ P)
variable (hRW : R ≤ W) (hPW : P ≤ W)
variable (hPcard : Nat.card P = 4)
variable (eR : R ≃* Multiplicative (GaloisField 2 4))
variable (eW : W ≃* (Multiplicative (GaloisField 2 4) × P))
variable (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
variable (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
variable (φ : P →* Multiplicative (GaloisField 2 4))
variable (hφ : Function.Injective φ)
variable (F : Set (Subgroup W))
variable (hF : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ a : GaloisField 2 4,
    Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
variable (hForbit : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ n : Subgroup.normalizer (W : Set G),
    Q = (W.normalizerMonoidHom n) • P.subgroupOf W)
variable (hNR : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (R : Set G))

local notation "F4" => GaloisField 2 4

local notation "Norm" => Subgroup.normalizer (W : Set G)

end

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216

open CFSG

noncomputable section

local notation "F4" => GaloisField 2 4

end

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216.RootCardinality

open scoped Pointwise
open CFSG.LieType.ChevTwo.OppCl

local notation "F16" => GaloisField 2 4

variable {R : Type*} [Group R] [Finite R]

private theorem card_F : Nat.card F16 = 16 := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

private noncomputable abbrev K4 : IntermediateField (ZMod 2) F16 :=
  (CFSG.RankTwoShapes.fieldSixteenSubfield card_F).toIntermediateField (by
    classical
    intro x
    fin_cases x
    · change (algebraMap (ZMod 2) F16) (0 : ZMod 2) ^ 4 =
        (algebraMap (ZMod 2) F16) (0 : ZMod 2)
      simp only [map_zero, zero_pow (by norm_num : 4 ≠ 0)]
    · change (algebraMap (ZMod 2) F16) (1 : ZMod 2) ^ 4 =
        (algebraMap (ZMod 2) F16) (1 : ZMod 2)
      simp only [map_one, one_pow])

private instance finite_K4 : Finite K4 :=
  Finite.of_injective (fun x : K4 => (x : F16)) (fun _ _ h => Subtype.ext h)

end CFSG.ComponentClassification.Foote47L216.RootCardinality

namespace CFSG.ComponentClassification.Foote47L216

open RootCardinality CFSG.LieType.ChevTwo.OppCl
open scoped Pointwise
local notation "F16" => GaloisField 2 4

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216.SingerIndex

open CFSG.ScalarGraphAction
open scoped Pointwise

local notation "F" => GaloisField 2 4

end CFSG.ComponentClassification.Foote47L216.SingerIndex

namespace CFSG.ComponentClassification.Foote47L216

open CFSG CFSG.ScalarGraphAction
open scoped Pointwise
noncomputable section
local notation "F4" => GaloisField 2 4

variable {G : Type} [Group G] [Finite G]
variable {W R P : Subgroup G}
variable (hW : W = R ⊔ P)
variable (hRW : R ≤ W) (hPW : P ≤ W)
variable (hPcard : Nat.card P = 4)
variable (eR : R ≃* Multiplicative F4)
variable (eW : W ≃* (Multiplicative F4 × P))
variable (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
variable (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
variable (φ : P →* Multiplicative F4)
variable (hφ : Function.Injective φ)
variable (F : Set (Subgroup W))
variable (hF : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ a : F4,
    Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
variable (hForbit : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ n : Subgroup.normalizer (W : Set G),
    Q = (W.normalizerMonoidHom n) • P.subgroupOf W)
variable (hNR : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (R : Set G))

local notation "Norm" => Subgroup.normalizer (W : Set G)

end

end CFSG.ComponentClassification.Foote47L216

namespace CFSG.ComponentClassification.Foote47L216

open CFSG CFSG.ScalarGraphAction
open scoped Pointwise

noncomputable section

local notation "F4" => GaloisField 2 4

variable {G : Type} [Group G] [Finite G]
variable {W R P : Subgroup G}
variable (hW : W = R ⊔ P)
variable (hRW : R ≤ W) (hPW : P ≤ W)
variable (hPcard : Nat.card P = 4)
variable (eR : R ≃* Multiplicative F4)
variable (eW : W ≃* (Multiplicative F4 × P))
variable (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
variable (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
variable (φ : P →* Multiplicative F4)
variable (hφ : Function.Injective φ)
variable (F : Set (Subgroup W))
variable (hF : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ a : F4,
    Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
variable (hForbit : ∀ Q : Subgroup W,
  Q ∈ F ↔ ∃ n : Subgroup.normalizer (W : Set G),
    Q = (W.normalizerMonoidHom n) • P.subgroupOf W)
variable (hNR : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (R : Set G))

local notation "Norm" => Subgroup.normalizer (W : Set G)

end

end CFSG.ComponentClassification.Foote47L216

