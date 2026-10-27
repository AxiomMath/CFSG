module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Main
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactBlockL28Rank_holds :
    KFactBlockL28Rank :=
  kFactBlockL28Rank_of_griess
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem kFactBlockL28TwoRank_holds :
    KFactBlockL28TwoRank :=
  kFactBlockL28TwoRank_of_griess
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
