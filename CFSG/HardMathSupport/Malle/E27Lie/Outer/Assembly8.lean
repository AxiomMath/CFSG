module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Assembly7
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Diag

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

section

set_option linter.unusedSectionVars false

theorem twistedE6InnerDiagLowerBound_holds :
    CFSG.HardMathSupport.Lang.E27.TwistedE6InnerDiagLowerBound :=
  fun {_ _} hℓ hf K _ _ hK σ hσ _ β hβ3 _ hβ =>
    CFSG.HardMathSupport.Lang.Coordinator.twentySeven_dvd_fixedSubgroup_twistedE6RootGroup
      hℓ hf K hK σ hσ β hβ3 hβ

theorem e27LieOuterAut_of_D4
    (hD4 : E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q)) :
    CFSG.HardMathSupport.Foote.E27.E27LieOuterAut :=
  e27LieOuterAut_of_open_two twistedE6InnerDiagLowerBound_holds hD4

end

end CFSG.HardMathSupport.Malle.E27Lie
