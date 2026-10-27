module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section Fin4

@[expose] def T4Supply : Prop :=
  ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → Thm4RTwinBelow 3 n

end Fin4

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
