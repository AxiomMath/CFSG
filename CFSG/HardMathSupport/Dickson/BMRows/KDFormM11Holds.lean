module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11
public import CFSG.HardMathSupport.Dickson.BMRows.KDFormM11

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Yardstones.Md0ec50421ce4 (YS02)

section YS02

theorem ys02_holds
    : YS02 :=
  ys02_of_B card_centralizer_eleven_B_le

end YS02

end CFSG.HardMathSupport.Dickson.BMRows
