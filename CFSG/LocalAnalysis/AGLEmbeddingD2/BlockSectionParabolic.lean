module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockNoncentralThree
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.AGLEmbeddingD2

theorem kFactBlockAltFiveSectionParabolic : KFactBlockAltFiveSectionParabolic :=
  kFactBlockAltFiveSectionParabolic_of CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverAlternating
    (CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)

end CFSG.AGLEmbeddingD2
