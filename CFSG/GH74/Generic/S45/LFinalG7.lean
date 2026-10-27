module

public import CFSG.GH74.Generic.S45.LFinalG6
public import CFSG.GH74.Generic.S45.LPsp4Class

public section

namespace CFSG.GH74.Generic.S45

open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

@[expose] def B_1310_odd_rest2_g4 : Prop :=
  OddRowG_PSU3 ∧ OddRowG_PSU4

theorem b_1310_odd_rest3_g4_of_rest2 (h : B_1310_odd_rest2_g4) : B_1310_odd_rest3_g4 :=
  ⟨h.1, h.2, oddRowG_PSp4⟩

end CFSG.GH74.Generic.S45
