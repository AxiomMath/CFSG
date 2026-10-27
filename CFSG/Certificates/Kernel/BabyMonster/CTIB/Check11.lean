module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Render
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data0
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data1
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data2
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data3
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data4
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data5
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data6
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data7
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data8
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data9
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data10
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data11
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data12
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data13
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data14
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data15
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data16
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data17
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data18
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data19
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data20
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data21
public import CFSG.Certificates.Kernel.BabyMonster.CTIB.Data22
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data7
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data8
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data10
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3

#bm_mul CFSG.KC.BM.CTIB cR3 CFSG.KC.BM.NativePair.Q0 [CFSG.KC.BM.Max2.E1 CFSG.KC.BM.Max2.E2] R3 []
#bm_mul CFSG.KC.BM.CTIB sq3 R3 [R3] I []
#bm_bool CFSG.KC.BM.CTIB rkr3_0 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s0) Pr3.s0) Qr3.s0)
#bm_bool CFSG.KC.BM.CTIB rkr3_1 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s1) Pr3.s1) Qr3.s1)
#bm_bool CFSG.KC.BM.CTIB rkr3_2 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s2) Pr3.s2) Qr3.s2)
#bm_bool CFSG.KC.BM.CTIB rkr3_3 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s3) Pr3.s3) Qr3.s3)
#bm_bool CFSG.KC.BM.CTIB rkr3_4 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s4) Pr3.s4) Qr3.s4)
#bm_bool CFSG.KC.BM.CTIB rkr3_5 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s5) Pr3.s5) Qr3.s5)
#bm_bool CFSG.KC.BM.CTIB rkr3_6 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s6) Pr3.s6) Qr3.s6)
#bm_bool CFSG.KC.BM.CTIB rkr3_7 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s7) Pr3.s7) Qr3.s7)
#bm_bool CFSG.KC.BM.CTIB rkr3_8 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s8) Pr3.s8) Qr3.s8)
#bm_bool CFSG.KC.BM.CTIB rkr3_9 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s9) Pr3.s9) Qr3.s9)
#bm_bool CFSG.KC.BM.CTIB rkr3_10 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s10) Pr3.s10) Qr3.s10)
#bm_bool CFSG.KC.BM.CTIB rkr3_11 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s11) Pr3.s11) Qr3.s11)
#bm_bool CFSG.KC.BM.CTIB rkr3_12 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s12) Pr3.s12) Qr3.s12)
#bm_bool CFSG.KC.BM.CTIB rkr3_13 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s13) Pr3.s13) Qr3.s13)
#bm_bool CFSG.KC.BM.CTIB rkr3_14 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s14) Pr3.s14) Qr3.s14)
#bm_bool CFSG.KC.BM.CTIB rkr3_15 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s15) Pr3.s15) Qr3.s15)
#bm_bool CFSG.KC.BM.CTIB rkr3_16 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s16) Pr3.s16) Qr3.s16)
#bm_bool CFSG.KC.BM.CTIB rkr3_17 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s17) Pr3.s17) Qr3.s17)
#bm_bool CFSG.KC.BM.CTIB rkr3_18 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s18) Pr3.s18) Qr3.s18)
#bm_bool CFSG.KC.BM.CTIB rkr3_19 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s19) Pr3.s19) Qr3.s19)
#bm_bool CFSG.KC.BM.CTIB rkr3_20 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s20) Pr3.s20) Qr3.s20)
#bm_bool CFSG.KC.BM.CTIB rkr3_21 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s21) Pr3.s21) Qr3.s21)
#bm_bool CFSG.KC.BM.CTIB rkr3_22 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s22) Pr3.s22) Qr3.s22)
#bm_bool CFSG.KC.BM.CTIB rkr3_23 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s23) Pr3.s23) Qr3.s23)
#bm_bool CFSG.KC.BM.CTIB rkr3_24 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s24) Pr3.s24) Qr3.s24)
#bm_bool CFSG.KC.BM.CTIB rkr3_25 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s25) Pr3.s25) Qr3.s25)
#bm_bool CFSG.KC.BM.CTIB rkr3_26 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s26) Pr3.s26) Qr3.s26)
#bm_bool CFSG.KC.BM.CTIB rkr3_27 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s27) Pr3.s27) Qr3.s27)
#bm_bool CFSG.KC.BM.CTIB rkr3_28 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s28) Pr3.s28) Qr3.s28)
#bm_bool CFSG.KC.BM.CTIB rkr3_29 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s29) Pr3.s29) Qr3.s29)
#bm_bool CFSG.KC.BM.CTIB rkr3_30 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s30) Pr3.s30) Qr3.s30)
#bm_bool CFSG.KC.BM.CTIB rkr3_31 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s31) Pr3.s31) Qr3.s31)
#bm_bool CFSG.KC.BM.CTIB rkr3_32 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R3 Pr3.s32) Pr3.s32) Qr3.s32)
