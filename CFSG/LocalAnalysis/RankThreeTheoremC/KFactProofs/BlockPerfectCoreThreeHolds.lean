module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeMain
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactBlockPerfectCoreThree_holds :
    KFactBlockPerfectCoreThree :=
  kFactBlockPerfectCoreThree_of_griess
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
