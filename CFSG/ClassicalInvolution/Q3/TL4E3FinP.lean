module

public import CFSG.ClassicalInvolution.Q3.TL4E3Fin
public import CFSG.ClassicalInvolution.Q3.TL4MF163A3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution

section Finish


theorem tightE3Z2Fin_proved (n : ℕ) : TightE3Z2Fin n :=
  tightE3Z2Fin_of modelL3U3Acts3_proved

theorem tightE3S3Fin_proved (n : ℕ) : TightE3S3Fin n :=
  tightE3S3Fin_of modelL3U3Acts3_proved

end Finish

end CFSG.ClassicalInvolution.Q3.TL4
