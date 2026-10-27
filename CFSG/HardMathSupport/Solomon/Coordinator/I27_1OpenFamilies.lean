module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

structure I271OpenFamilies : Prop where
  nnHatSixRank : I271NNHatSixRank
  nnOther : I271NNOther
  altDiv : I271AltDiv
  altNdiv : I271AltNdiv
  chevPBal : I271ChevPBal
  chevPExc : I271ChevPExc
  sporGen : I271SporGen
  autBalanceON : I271AutBalanceON
  onLow : I271ONLow
  chevQL34 : I271ChevQLThreeFour
  chevQ : I271ChevQ

end CFSG.HardMathSupport.Solomon.Coordinator
