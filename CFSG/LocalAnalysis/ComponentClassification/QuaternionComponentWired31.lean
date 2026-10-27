module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired27

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

section Wired

theorem lambdaComm₃₁
    (n : ℕ) : Q3.TL4.PlusLeaf Q3.TL4.TightLambdaCommR n := fun hA hP =>
  Q3.TL4.tightLambdaCommR_three_of_plus hP hA (thm4RBelow₂₇ n hA hP) Q3.TL4.secIdE4OddCent_proved

end Wired

end CFSG.ComponentClassification.QuaternionComponent
