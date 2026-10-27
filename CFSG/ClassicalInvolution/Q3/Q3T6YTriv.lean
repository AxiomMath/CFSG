module

public import CFSG.ClassicalInvolution.Q3.Q3T6YStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6XTriv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem diagInputTrivOn_of_noTrivialSwapOn {S : Set F} (h : NoTrivialSwapOn F S) :
    DiagInputTrivOn F S := by
  intro Q r u hQ hrS huS hu2 hur hne I hI htriv q _ _ _
  exact absurd htriv (h hQ hrS huS hu2 hur hne hI)

end CFSG.ClassicalInvolution.Q3.Q3T6Y
