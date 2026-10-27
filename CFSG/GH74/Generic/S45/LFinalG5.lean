module

public import CFSG.GH74.Generic.S45.LFinalG4
public import CFSG.GH74.Generic.S45.LOddPSL4

public section

namespace CFSG.GH74.Generic.S45

open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

@[expose] def B_1310_odd_rest4_g4 : Prop :=
  OddRowG_PSL3 ∧ OddRowG_PSU3 ∧ OddRowG_PSU4 ∧ OddRowG_PSp4

theorem b_1310_odd_rest5_g4_of_rest4 (h : B_1310_odd_rest4_g4) : B_1310_odd_rest5_g4 :=
  ⟨h.1, oddRowG_PSL4, h.2.1, h.2.2.1, h.2.2.2⟩

end CFSG.GH74.Generic.S45
