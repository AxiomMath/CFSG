module

public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired33
public import CFSG.ClassicalInvolution.Q3.TL4ExitDich
public import CFSG.ClassicalInvolution.Q3.TL4S289U4
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3Q
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OG

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

section Wired

theorem star289TFree₃₆
    (hGH : GH74SectionalModels) : ∀ n, Q3.TL4.TightStar289TFreeR 3 n :=
  fun n Y _ _ R S t hL => Q3.TL4.tightStar289TFreeR_of Q3.TL4.omegaAutOddFreeR_proved
    Q3.TL4.secIdExitDich3_proved
    (Q3.TL4.secIdExitS3IdentF_of Q3.TL4.secIdE3MuS3_proved Q3.TL4.secIdE3L2NoStar_proved n
      (thm6RBelow_of_large₃₃ hGH hL)) Y R S t hL

end Wired

end CFSG.ComponentClassification.QuaternionComponent
