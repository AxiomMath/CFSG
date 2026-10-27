module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixAltHolds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC


theorem agl81FiveTwentySix_of_alt
    {G : Type} [Group G] [Finite G]
    (hAlt : AGL81FiveTwentySixAlt) : AGL81FiveTwentySix G :=
  agl81FiveTwentySix_of KFactProofs.ffModuleTheorem_holds
    (CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516_of_graphOrbit
      CFSG.AGLEmbeddingD2.Tits.GN516.kFactChevGraphOrbit_proved
      CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516SymOver_holds)
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.kFactChevGenThree_proved
    gnAltFacts_holds hAlt

theorem agl81FiveTwentySix_holds
    {G : Type} [Group G] [Finite G] : AGL81FiveTwentySix G :=
  agl81FiveTwentySix_of_alt agl81FiveTwentySixAlt_holds

end CFSG.LocalAnalysis.RankThreeTheoremC
