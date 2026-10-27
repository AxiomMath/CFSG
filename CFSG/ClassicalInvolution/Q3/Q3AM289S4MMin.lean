module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MKit
public import CFSG.ClassicalInvolution.Q3.Q3MFODMinus
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.Q3.Q3AMPspLeaves
public import CFSG.ClassicalInvolution.Q3.Q3AMTri
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Assembly.LowTwoRank


theorem s4VertexModelLeafAt_minus4 : S4VertexModelLeafAt (CompData.model .POmegaMinus 4) :=
  s4VertexAt_of_fixedOddFreeFund (t := .POmegaMinus) (n := 4) trivial
    ⟨Nat.prime_three, le_rfl, le_rfl⟩ (by decide) (by decide) (fun h => by cases h.1)
    Q3PP.fixedOddFreeFund_minus4

end CFSG.ClassicalInvolution.Q3.Q3AM
