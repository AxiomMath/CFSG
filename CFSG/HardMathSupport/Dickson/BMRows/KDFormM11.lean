module

public import CFSG.HardMathSupport.Dickson.BMRows.M11Rows
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02K5
public import CFSG.HardMathSupport.Dickson.BMRows.M13Rows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA
open CFSG.Yardstones.Md0ec50421ce4 (YS02)
open CFSG.HardMathSupport.Timmesfeld.Proving (sporadicOuterLeTwo_holds)

section YS02

theorem ys02_of_B
    (hB : ∀ y : NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.B)) ≤ 1320) :
    YS02 :=
  ys02_of_m11_m13 (kdSporRow_M_eleven (M11.centElevenBound_of_B hB))
      CFSG.HardMathSupport.Dickson.BMRows.kdSporRow_M_thirteen

end YS02

end CFSG.HardMathSupport.Dickson.BMRows
