module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KISId
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.O812six

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

theorem o812sixGen_of_fi22
    (hFi22 : KFactFi22SPEThreeRank) : Section15.O812sixGen :=
  o812sixGen_of_inputs
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
    (stronglyEmbeddedSolvableId_of_kFacts
        CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
        CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieTorus_holds
        CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 hFi22) CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
