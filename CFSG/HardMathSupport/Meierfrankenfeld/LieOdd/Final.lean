module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Exceptional
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallPSp47
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallPSp63
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallPSp83
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Omega73Cover
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallU53
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallG23

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem gf2NoFFLieOddSmall_of_smallU43
    (hU43 : SmallU43) : GF2NoFFLieOddSmall :=
  gf2NoFFLieOddSmall_of_cells smallPSp45 smallPSp47 smallOmega73 smallPSp63 smallPSp83 hU43
    smallU53 smallG23

theorem gf2NoFFLieOdd_of_smallU43
    (hU43 : SmallU43) : GF2NoFFLieOdd :=
  gf2NoFFLieOdd_of_small (gf2NoFFLieOddSmall_of_cells smallPSp45 smallPSp47 smallOmega73
    smallPSp63 smallPSp83 hU43 smallU53 smallG23)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
