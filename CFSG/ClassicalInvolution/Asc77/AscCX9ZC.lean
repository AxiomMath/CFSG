module

public import CFSG.ClassicalInvolution.Asc77.AscCX9ZB
public import CFSG.ClassicalInvolution.Asc77.AscCX9V
public import CFSG.ClassicalInvolution.Asc77.AscC5P3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

variable {p f : ℕ} [Fact p.Prime]


theorem om6ReflDiag_proved : Om6ReflDiag p f :=
  om6ReflDiag_of om5StabDiag_proved om6ReflWit_proved



theorem centExt_proved : C25W.CentExt p f :=
  centExt_of_om6ReflDiag om6ReflDiag_proved

end CFSG.ClassicalInvolution.Asc77.CX
