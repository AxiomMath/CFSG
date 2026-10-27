module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OB2
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OE
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OA
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OCD

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


theorem E3S3O.tightE3S3OConfig_proved {n : ℕ} (h4 : Thm4RBelow 3 n)
    (hOrb : TightE3S3Orbit n) : TightE3S3OConfig n :=
  E3S3O.tightE3S3OConfig_of_steps E3S3O.stepW_proved E3S3O.stepA_proved E3S3O.stepB_proved
    E3S3O.stepC_proved E3S3O.stepD_proved E3S3O.stepE_proved h4 hOrb

theorem tightE3S3Orth_of {n : ℕ} (h4 : Thm4RBelow 3 n) (hOm : Model1524Twin3Om)
    (hE4 : Model1524Twin3E4) (hOrb : TightE3S3Orbit n) : TightE3S3Orth n :=
  tightE3S3Orth_of_config hOm hE4 (E3S3O.tightE3S3OConfig_proved h4 hOrb)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
