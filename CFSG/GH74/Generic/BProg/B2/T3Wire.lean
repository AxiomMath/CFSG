module

public import CFSG.GH74.Generic.BProg.B2.T3WireCore
public import CFSG.GH74.Generic.BProg.B2.FixFourS3U
public import CFSG.GH74.Generic.BProg.B2.Thm2Done

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg

theorem stage2Thm3_of_S1
    (hS1 : Stage2Thm3S1) : Stage2Thm3 :=
  T3Wire.stage2Thm3_of_S1_of centerlessS345 involFixFour_shape3_proved involFixFour_shape4
    involFixFour_shape5 FixFourS3.fourConj_shape3 fourConj_shape4 fourConj_shape5 noJPrimeNonSD
    SDR.stage2SDRankC stage2Thm2C_proved hS1

end CFSG.GH74.Generic.BProg.B2
