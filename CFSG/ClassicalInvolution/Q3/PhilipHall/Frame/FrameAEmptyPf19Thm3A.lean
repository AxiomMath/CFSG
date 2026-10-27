module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ComponentClassification.AS76b

namespace Thm3A

section Rows

variable {Y : Type} [Group Y]

@[expose] def Thm3RowsA (Ω : Set (Subgroup Y)) (P : Subgroup Y) : Prop :=
  Thm3RowU3 P ∨ Thm3RowM12 P ∨ Thm3RowL3E8 P ∨ Thm3RowW Ω P

end Rows

end Thm3A

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
