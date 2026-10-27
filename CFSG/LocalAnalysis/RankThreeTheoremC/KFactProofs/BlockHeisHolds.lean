module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisReduce
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisAltSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisPSU54
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamA
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamARank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamD
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisG2
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactBlockHeisenbergAut_holds
    : KFactBlockHeisenbergAut := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  exact kFactBlockHeisenbergAut_of_cores heisCoreAlt_holds heisCoreSmall_holds
    (heisCoreOn_idxA_of_rank_facts (heisARankFacts_holds hGA))
    (heisCoreOn_idxTwistedA_of_rank_facts heisURankFacts_holds) (heisCoreOn_idxB hGA)
    (heisCoreOn_idxD hGA) (heisCoreOn_idxTwistedD hGA) (heisCoreOn_g2 hGA)
    psu54ParabolicFive_holds

theorem kFactBlockHeisenbergInner_holds
    : KFactBlockHeisenbergInner := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  exact kFactBlockHeisenbergInner_of_cores heisCoreAlt_holds heisCoreSmall_holds
    (heisCoreOn_idxA_of_rank_facts (heisARankFacts_holds hGA))
    (heisCoreOn_idxTwistedA_of_rank_facts heisURankFacts_holds) (heisCoreOn_idxB hGA)
    (heisCoreOn_idxD hGA) (heisCoreOn_idxTwistedD hGA) (heisCoreOn_g2 hGA)
    psu54ParabolicFive_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
