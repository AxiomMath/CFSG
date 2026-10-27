module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsMain
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsONFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAltDiv
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsChevPExc
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNOther
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

section Assembly

set_option linter.unusedSectionVars false


theorem i271OpenFamilies_of_three
    (hChevPBal : I271ChevPBal) (hSporGen : I271SporGen) (hChevQ : I271ChevQ) :
    I271OpenFamilies :=
  i271OpenFamilies_of_rest
      (i271NNOther_holds CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
          CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
          CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds) i271AltDiv_holds hChevPBal
      i271ChevPExc_holds hSporGen i271AutBalanceON_holds hChevQ

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator
