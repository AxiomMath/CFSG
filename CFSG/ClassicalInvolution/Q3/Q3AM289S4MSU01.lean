module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MKit
public import CFSG.ClassicalInvolution.Q3.Q3MFOPSU4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Assembly.LowTwoRank


theorem s4VertexModelLeafAt_psu4 : S4VertexModelLeafAt (CompData.model .PSU 4) :=
  s4VertexAt_of_fixedOddFreeFund (t := .PSU) (n := 4) trivial
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩ (by decide) (by decide)
    (fun h => by cases h.1) Q3PP.fixedOddFreeFund_psu4

end CFSG.ClassicalInvolution.Q3.Q3AM
