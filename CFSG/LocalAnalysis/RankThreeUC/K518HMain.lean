module

public import CFSG.LocalAnalysis.RankThreeUC.K518HRed
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518Res
public import CFSG.LocalAnalysis.RankThreeUC.K518HAMain
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkSL2
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkSU3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YProof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenThree

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

theorem k518Crit_holds :
    K518Crit :=
  k518Crit_of_rk k518RkSL2_holds k518RkSU3_holds

theorem kFact518Out_holds :
    CFSG.LocalAnalysis.RankThreeUC.S15.KFact518Out :=
  kFact518Out_of_crit k518Crit_holds

theorem k518Y_holds :
    CFSG.LocalAnalysis.RankThreeUC.S15.K518Y :=
  k518Y_of_cover (fun _ _ _ _ _ _ _ hg => hg.cover.1)
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.kFactChevGenThree_proved kFact518Out_holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
