module

public import CFSG.ClassicalInvolution.Asc77.AscC22P8
import CFSG.ClassicalInvolution.Asc77.AscSCH28

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]


theorem c22_chainPos_of_alpha (hα : C22P.C22_alpha p f) : R31.C22_chainPos p f :=
  C22P.c22_chainPos_of_alpha SCH.oddCenterClassical hα

end CFSG.ClassicalInvolution.Asc77
