module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1OpenFamilies
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL34
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsON
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSix
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

section Assembly

set_option linter.unusedSectionVars false



theorem i271OpenFamilies_of_rest
    (hNNOther : I271NNOther) (hAltDiv : I271AltDiv) (hChevPBal : I271ChevPBal)
    (hChevPExc : I271ChevPExc) (hSporGen : I271SporGen) (hAutBalanceON : I271AutBalanceON)
    (hChevQ : I271ChevQ) : I271OpenFamilies where
  nnHatSixRank := i271NNHatSixRank_holds
  nnOther := hNNOther
  altDiv := hAltDiv
  altNdiv := i271AltNdiv_holds
  chevPBal := hChevPBal
  chevPExc := hChevPExc
  sporGen := hSporGen
  autBalanceON := hAutBalanceON
  onLow := i271ONLow_holds
  chevQL34 := i271ChevQLThreeFour_holds
  chevQ := hChevQ

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator
