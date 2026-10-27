module

public import CFSG.GH74.Generic.S45.LFinalG7
public import CFSG.GH74.Generic.S45.LPsu3

public section

namespace CFSG.GH74.Generic.S45

@[expose] def B_1310_odd_rest1_g4 : Prop :=
  OddRowG_PSU4

theorem b_1310_odd_rest2_g4_of_rest1 (h : B_1310_odd_rest1_g4) : B_1310_odd_rest2_g4 :=
  ⟨oddRowG_PSU3, h⟩

theorem b_1310_odd_rest_g4_of_rest1
    (h : B_1310_odd_rest1_g4) : B_1310_odd_rest_g4 :=
  b_1310_odd_rest_g4_of_rest6 <| b_1310_odd_rest6_g4_of_rest5 <| b_1310_odd_rest5_g4_of_rest4 <|
    b_1310_odd_rest4_g4_of_rest3 <| b_1310_odd_rest3_g4_of_rest2 <|
      b_1310_odd_rest2_g4_of_rest1 h

end CFSG.GH74.Generic.S45
