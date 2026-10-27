module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovMain
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem inputCoverFixedCentre_holds :
    InputCoverFixedCentre :=
  inputCoverFixedCentre_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem gap515CentreK_holds :
    LocalBalance.Lemma514Ns.Gap515CentreK :=
  gap515CentreK_of_inputCoverFixedCentre inputCoverFixedCentre_holds

end CFSG.HardMathSupport.Solomon.Coordinator
