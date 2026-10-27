module

public import CFSG.HardMathSupport.Dickson.BMRows.KFormRowsBM
public import CFSG.HardMathSupport.Dickson.BMRows.M11Rows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA

theorem i1416Chev2SporListK_of_B
    (hB : ∀ y : NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.B)) ≤ 1320) :
    I1416Chev2SporListK :=
  i1416Chev2SporListK_of_rows (crow_M_eleven (M11.centElevenBound_of_B hB))

end CFSG.HardMathSupport.Dickson.BMRows
