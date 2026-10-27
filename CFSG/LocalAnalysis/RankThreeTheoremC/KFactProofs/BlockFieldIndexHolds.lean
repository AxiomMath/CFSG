module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexLinearDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexSymp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexOrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexOrthMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexG2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexSmall
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding FieldIndex

theorem fieldIndexOn_symp (hGA : GriessAllModelsStatement) :
    FieldIndexOn (IsLieOf IdxB) :=
  fieldIndexOn_of_outPNice (fun _ _ _ _ _ _ hC _ => outPNice_three_of_idxB hC)
    (leviInnOn_symp hGA)

theorem kFactCompParabFieldIndex_of_griess
    (hGA : GriessAllModelsStatement) : KFactCompParabFieldIndex :=
  kFactCompParabFieldIndex_of_families (fieldIndexOn_linear hGA) fieldIndexOn_unitary
    (fieldIndexOn_symp hGA) (fieldIndexOn_orthPlus hGA) (fieldIndexOn_orthMinus hGA)
    (fieldIndexOn_g2 hGA) (fieldIndexOn_small hGA)

theorem kFactCompParabFieldIndex_holds
    : KFactCompParabFieldIndex :=
  kFactCompParabFieldIndex_of_griess
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem kFactBlockFieldIndex_holds
    : KFactBlockFieldIndex :=
  kFactBlockFieldIndex_of kFactCompParabFieldIndex_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
