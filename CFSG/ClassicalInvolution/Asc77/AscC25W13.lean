module

public import CFSG.ClassicalInvolution.Asc77.AscC25W5
public import CFSG.ClassicalInvolution.Asc77.AscC25W12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace C25W

variable {p f : ℕ} [Fact p.Prime]

theorem c25_9_of_centExt (hM6 : C25Y.Layer6Cen4 p f) (hExt : CentExt p f) : C25_9 p f :=
  c25_9_of_residuals hM6 layer5Sq_proved hExt

end C25W

end CFSG.ClassicalInvolution.Asc77
