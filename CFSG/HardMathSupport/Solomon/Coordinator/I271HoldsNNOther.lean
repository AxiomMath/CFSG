module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNSL
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNM22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem i271NNOther_holds
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) :
    I271NNOther :=
  i271NNOther_of_types (nnL2OddPow_holds T TL TT)
    (nnHatMTwentyTwo_holds T TL TT) (nnSLThreeExc_holds T TL TT) (nnSUThreeExc_holds T TL TT)

end CFSG.HardMathSupport.Solomon.Coordinator
