module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Final
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Final
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43F3
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutIndex

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem smallU43 :
    SmallU43 :=
  smallU43_of U43Out.u43F3 u43_outElemIndexLE

theorem gf2NoFFLieOddSmall :
    GF2NoFFLieOddSmall :=
  gf2NoFFLieOddSmall_of_smallU43 smallU43

theorem gf2NoFFLieOdd :
    GF2NoFFLieOdd :=
  gf2NoFFLieOdd_of_smallU43 smallU43

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
