module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Cases
public import CFSG.LocalAnalysis.RankThreeUC.K37HBBal207
public import CFSG.LocalAnalysis.RankThreeUC.K37HBChev
public import CFSG.LocalAnalysis.RankThreeUC.K37HBSporJ3
public import CFSG.LocalAnalysis.RankThreeUC.K37HBSporMcL
public import CFSG.LocalAnalysis.RankThreeUC.K37HGM22
public import CFSG.LocalAnalysis.RankThreeUC.K37HGON
public import CFSG.LocalAnalysis.RankThreeUC.K37HGSeven
public import CFSG.LocalAnalysis.RankThreeUC.K37HGU38
public import CFSG.LocalAnalysis.RankThreeUC.K37HR1
public import CFSG.LocalAnalysis.RankThreeUC.K37HR13
public import CFSG.LocalAnalysis.RankThreeUC.K37HR15
public import CFSG.LocalAnalysis.RankThreeUC.K37HR2
public import CFSG.LocalAnalysis.RankThreeUC.K37HR6
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoL28
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37


theorem kFactThreeSevenTwoThree_holds :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeSevenTwoThree :=
  kFactThreeSevenTwoThree_of_inputs (K37H.k37Rest_of_families K37H.k37Rest₁_holds
      K37H.k37Rest₂Two_holds K37H.k37Rest₂U38_holds K37H.k37Rest₃_holds K37H.k37Rest₄_holds
      K37H.k37Rest₅_holds K37H.k37Rest₆_holds K37H.k37Rest₇_holds K37H.k37Rest₈_holds
      K37H.k37Rest₉_holds K37H.k37Rest₁₀_holds K37H.k37Rest₁₁_holds K37H.k37Rest₁₂_holds
      K37H.k37Rest₁₃_holds K37H.k37Rest₁₄_holds K37H.k37Rest₁₅_holds)
    CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.AGLEmbedding.kFactCaseTwoNoTwoL28
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.kFactThreeFiveInner_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.k36OddDefChar_holds
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.k315Spor_holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
