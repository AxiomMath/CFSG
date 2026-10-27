module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Ident

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

@[expose] def InspectionFacts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], S7Ident.TwoOrbitModelS7 Y →
    ∀ K ∈ {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)},
      Thm3RConclG {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)} K

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7
