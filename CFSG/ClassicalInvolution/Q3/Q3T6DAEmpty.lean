module

public import CFSG.ClassicalInvolution.Q3.Q3T6DCore
public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIC
public import CFSG.ClassicalInvolution.Q3.Q3T6DSMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ComponentClassification.AS76b

section AEmpty


theorem aEmptyDU_three_of_hyp51At (hΩ : HypOmegaModDU 3 1) (h4 : Asc75Theorem4)
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n) (hH : Res20_7Hyp51AtThree)
    (hP1 : Res10bP1Three) : AEmptyDU 3 1 :=
  aEmptyDU_three_of_cases hΩ (caseI3_of h4) hih (t3CaseII3_of_hyp51At hH hP1)

end AEmpty

end CFSG.ClassicalInvolution.Q3.Q3T6D
