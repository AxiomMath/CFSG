module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Gen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Aux
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Setup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz
public import Certificates.Certificate2246
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Inputs


theorem L630.l613f3_of_inputs (h291 : KD291a3) : L630.L613f3 :=
  L630.l613f3_of_facts CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (kFactBetaStructure_holds K713S.kFactSylowSplit_holds) h291
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds

theorem l613_of_inputs (h291 : KD291a3) (hr : KFact613rankP) : L613 :=
  l613_of_facts CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (kFactBetaStructure_holds K713S.kFactSylowSplit_holds) h291 hr
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds

end Inputs

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
