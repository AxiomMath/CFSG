module

public import CFSG.GH74.Generic.S45.LPsl2Row
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public section

namespace CFSG.GH74.Generic.S45

open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

@[expose] def B_1310_odd_rest6_g4 : Prop :=
  OddRowG_PSL3 ∧ OddRowG_PSL4 ∧ OddRowG_PSL5 ∧ OddRowG_PSU3 ∧ OddRowG_PSU4 ∧ OddRowG_PSp4

theorem b_1310_odd_rest_g4_of_rest6
    (h : B_1310_odd_rest6_g4) : B_1310_odd_rest_g4 :=
  ⟨oddRowG_PSL2, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end CFSG.GH74.Generic.S45
