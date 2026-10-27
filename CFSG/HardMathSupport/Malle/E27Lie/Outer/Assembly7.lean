module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Assembly6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagFinal

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

section

theorem e6InnerDiagLowerBound_holds : CFSG.HardMathSupport.Lang.E27.E6InnerDiagLowerBound :=
  fun {_ _} [Fact _] hf K _ hK _ g a hα3 hα =>
    CFSG.HardMathSupport.Lang.E6Descent.twentySeven_dvd_fixedSubgroup_E6 hf K hK _ hα3 hα

theorem e27LieOuterAut_of_open_two
    (htE6 : CFSG.HardMathSupport.Lang.E27.TwistedE6InnerDiagLowerBound)
    (hD4 : E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q)) :
    CFSG.HardMathSupport.Foote.E27.E27LieOuterAut :=
  e27LieOuterAut_of_open_three e6InnerDiagLowerBound_holds htE6 hD4

end

end CFSG.HardMathSupport.Malle.E27Lie
