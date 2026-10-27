module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.NineThreeThreeTPLT
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB


theorem kFactBlockE9Transitive_holds
    : KFactBlockE9Transitive :=
  E9Transitive.kFactBlockE9Transitive_of asc81bNineThree_holds
      (AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.kFactNineThreeThreeBig_of_two
          (AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.kFactNineThreeThreeTwo_of_tplt
              CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds))
      kFactBlockPLElem_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB
