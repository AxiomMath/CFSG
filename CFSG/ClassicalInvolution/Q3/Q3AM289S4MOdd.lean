module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MKit
public import CFSG.ClassicalInvolution.Q3.Q3MFOSOdd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Assembly.LowTwoRank


theorem s4VertexModelLeafAt_odd3 : S4VertexModelLeafAt (CompData.model .POmegaOdd 3) :=
  s4VertexAt_of_fixedOddFreeFund (t := .POmegaOdd) (n := 3) trivial
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩ (by decide) (by decide)
    (fun h => by cases h.1)
    (Q3PP.FixedOddFree.toFund
      (Q3MFO.fixedOddFree_pOmegaOdd ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩))

end CFSG.ClassicalInvolution.Q3.Q3AM
