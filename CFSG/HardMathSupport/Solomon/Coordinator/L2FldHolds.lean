module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldReduce
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldCentre
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem l2CentreThree_holds :
    L2CentreThree :=
  l2CentreThree_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem inputL2fld_holds :
    LocalBalance.Lemma514CoverNs.InputL2fld :=
  inputL2fld_of_facts Proving.l2OrderUnique_holds l2Aut3Classification_holds l2FieldFixed_holds
    l2CentreThree_holds

end CFSG.HardMathSupport.Solomon.Coordinator
