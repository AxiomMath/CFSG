module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankCore
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem inputD4_of_griess (hG : GriessAllModelsStatement) : LocalBalance.Lemma27Ns.InputD4 :=
  inputD4_of_core hG lbid4Core_holds

theorem inputD4_holds :
    LocalBalance.Lemma27Ns.InputD4 :=
  inputD4_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.HardMathSupport.Solomon.Coordinator
