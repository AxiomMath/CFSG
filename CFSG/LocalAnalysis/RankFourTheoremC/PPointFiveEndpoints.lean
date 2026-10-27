module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFiveReduction
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate110
public import Certificates.Certificate19762
public import Certificates.Certificate19763
public import Certificates.Certificate2191
public import Certificates.Certificate2192

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (gl83NormalElementaryRankFour_holds)


theorem theoremCRankFour_of_five_endpoints' (hD1 : D1Rank4) (hD2 : D2Rank4)
    (hFC : FullCoreRank4) (hDich : DichotomyRank4Five) (hE2 : E2NonstrongRank4Five)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList)
    (hsig : GL83SignalizerAut) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h713 : GL83.I_7_13_1) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) : GLBUniqueFour G :=
  theoremCRankFour_of_five_endpoints hD1 hD2 hFC hDich hE2 h243 h244 hsig
    gl83NormalElementaryRankFour_holds kFactReeBorelMaximal kFactReeInvolution hInn hWC h713 G
    hnonab hK hchar he hpre

end CFSG.LocalAnalysis.RankFourTheoremC
