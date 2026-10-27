module

public import CFSG.ClassicalInvolution.Asc77.AscCX8E
public import CFSG.ClassicalInvolution.Asc77.AscCX4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

variable {p f : ℕ} [Fact p.Prime]

theorem centExt_of_noMixParity' (h : NoMixParity p f) : C25W.CentExt p f :=
  centExt_of_noMixParity (layer6Twin_proved p f) h

end CFSG.ClassicalInvolution.Asc77.CX
