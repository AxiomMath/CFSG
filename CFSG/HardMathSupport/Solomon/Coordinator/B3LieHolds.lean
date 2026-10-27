module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieDC
public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator


theorem b3SimpleLie_of_open (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : B3SimpleLie :=
  b3SimpleLie_of_defChar defCharInnerCoreFree_holds hss hout

theorem input14_5Lie_of_open (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : Input14_5Lie :=
  input14_5Lie_of_defChar defCharInnerCoreFree_holds hss hout

end CFSG.HardMathSupport.Solomon.Coordinator
