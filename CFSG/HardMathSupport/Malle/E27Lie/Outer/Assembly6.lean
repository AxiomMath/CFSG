module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Assembly5
public import CFSG.HardMathSupport.Lang.E27Lie.MinusToral
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Assembly
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagThree
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldX2Index
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexU3
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexE6

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open TauCeti

section


theorem e27LieOuterAutAt_trialityD4_all :
    E27LieOuterAutAt (fun i => ∃ q, i = .trialityD4 q) :=
  e27LieOuterAutAt_trialityD4 CFSG.HardMathSupport.Lang.E27Lie.minusToralLower_holds
    trialityThreeLower_holds

theorem e27LieOuterAut_of_open_three
    (hE6 : CFSG.HardMathSupport.Lang.E27.E6InnerDiagLowerBound)
    (htE6 : CFSG.HardMathSupport.Lang.E27.TwistedE6InnerDiagLowerBound)
    (hD4 : E27LieOuterAutAt (fun i => ∃ q, i = .D 4 q)) :
    CFSG.HardMathSupport.Foote.E27.E27LieOuterAut :=
  e27LieOuterAut_of_families linearDiagSlice_holds unitaryRestSlice_holds
      e27LieOuterAutAt_B_two_even hD4 (e27LieOuterAutAt_E6 hE6) (e27LieOuterAutAt_twistedE6 htE6)
      e27LieOuterAutAt_trialityD4_all

end

end CFSG.HardMathSupport.Malle.E27Lie
