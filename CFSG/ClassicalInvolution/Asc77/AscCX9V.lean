module

public import CFSG.ClassicalInvolution.Asc77.AscCX9U
public import CFSG.ClassicalInvolution.Asc77.AscC5P2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem parityE4_of_om6ReflDiag (h2 : Om6ReflDiag p f) : ParityE4 p f :=
  parityE4_of diagThree_proved h2


theorem centExt_of_om6ReflDiag (h2 : Om6ReflDiag p f) : C25W.CentExt p f :=
  centExt_of_parityE4 (parityE4_of_om6ReflDiag h2)

end Final

end CFSG.ClassicalInvolution.Asc77.CX
