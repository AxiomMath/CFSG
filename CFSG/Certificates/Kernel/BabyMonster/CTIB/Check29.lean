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

#bm_mul CFSG.KC.BM.CTIB cR10 CFSG.KC.BM.Max2.G1 [CFSG.KC.BM.Max2.E7] R10 []
#bm_mul CFSG.KC.BM.CTIB sq10 R10 [R10] I []
#bm_bool CFSG.KC.BM.CTIB rkr10_0 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s0) Pr10.s0) Qr10.s0)
#bm_bool CFSG.KC.BM.CTIB rkr10_1 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s1) Pr10.s1) Qr10.s1)
#bm_bool CFSG.KC.BM.CTIB rkr10_2 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s2) Pr10.s2) Qr10.s2)
#bm_bool CFSG.KC.BM.CTIB rkr10_3 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s3) Pr10.s3) Qr10.s3)
#bm_bool CFSG.KC.BM.CTIB rkr10_4 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s4) Pr10.s4) Qr10.s4)
#bm_bool CFSG.KC.BM.CTIB rkr10_5 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s5) Pr10.s5) Qr10.s5)
#bm_bool CFSG.KC.BM.CTIB rkr10_6 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s6) Pr10.s6) Qr10.s6)
#bm_bool CFSG.KC.BM.CTIB rkr10_7 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s7) Pr10.s7) Qr10.s7)
#bm_bool CFSG.KC.BM.CTIB rkr10_8 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s8) Pr10.s8) Qr10.s8)
#bm_bool CFSG.KC.BM.CTIB rkr10_9 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s9) Pr10.s9) Qr10.s9)
#bm_bool CFSG.KC.BM.CTIB rkr10_10 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s10) Pr10.s10) Qr10.s10)
#bm_bool CFSG.KC.BM.CTIB rkr10_11 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s11) Pr10.s11) Qr10.s11)
#bm_bool CFSG.KC.BM.CTIB rkr10_12 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s12) Pr10.s12) Qr10.s12)
#bm_bool CFSG.KC.BM.CTIB rkr10_13 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s13) Pr10.s13) Qr10.s13)
#bm_bool CFSG.KC.BM.CTIB rkr10_14 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s14) Pr10.s14) Qr10.s14)
#bm_bool CFSG.KC.BM.CTIB rkr10_15 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s15) Pr10.s15) Qr10.s15)
#bm_bool CFSG.KC.BM.CTIB rkr10_16 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s16) Pr10.s16) Qr10.s16)
#bm_bool CFSG.KC.BM.CTIB rkr10_17 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s17) Pr10.s17) Qr10.s17)
#bm_bool CFSG.KC.BM.CTIB rkr10_18 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s18) Pr10.s18) Qr10.s18)
#bm_bool CFSG.KC.BM.CTIB rkr10_19 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s19) Pr10.s19) Qr10.s19)
#bm_bool CFSG.KC.BM.CTIB rkr10_20 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s20) Pr10.s20) Qr10.s20)
#bm_bool CFSG.KC.BM.CTIB rkr10_21 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s21) Pr10.s21) Qr10.s21)
#bm_bool CFSG.KC.BM.CTIB rkr10_22 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s22) Pr10.s22) Qr10.s22)
#bm_bool CFSG.KC.BM.CTIB rkr10_23 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s23) Pr10.s23) Qr10.s23)
#bm_bool CFSG.KC.BM.CTIB rkr10_24 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s24) Pr10.s24) Qr10.s24)
#bm_bool CFSG.KC.BM.CTIB rkr10_25 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s25) Pr10.s25) Qr10.s25)
#bm_bool CFSG.KC.BM.CTIB rkr10_26 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s26) Pr10.s26) Qr10.s26)
#bm_bool CFSG.KC.BM.CTIB rkr10_27 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s27) Pr10.s27) Qr10.s27)
#bm_bool CFSG.KC.BM.CTIB rkr10_28 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s28) Pr10.s28) Qr10.s28)
#bm_bool CFSG.KC.BM.CTIB rkr10_29 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s29) Pr10.s29) Qr10.s29)
#bm_bool CFSG.KC.BM.CTIB rkr10_30 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s30) Pr10.s30) Qr10.s30)
#bm_bool CFSG.KC.BM.CTIB rkr10_31 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s31) Pr10.s31) Qr10.s31)
#bm_bool CFSG.KC.BM.CTIB rkr10_32 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s32) Pr10.s32) Qr10.s32)
#bm_bool CFSG.KC.BM.CTIB rkr10_33 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s33) Pr10.s33) Qr10.s33)
#bm_bool CFSG.KC.BM.CTIB rkr10_34 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s34) Pr10.s34) Qr10.s34)
#bm_bool CFSG.KC.BM.CTIB rkr10_35 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s35) Pr10.s35) Qr10.s35)
#bm_bool CFSG.KC.BM.CTIB rkr10_36 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s36) Pr10.s36) Qr10.s36)
#bm_bool CFSG.KC.BM.CTIB rkr10_37 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s37) Pr10.s37) Qr10.s37)
#bm_bool CFSG.KC.BM.CTIB rkr10_38 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s38) Pr10.s38) Qr10.s38)
#bm_bool CFSG.KC.BM.CTIB rkr10_39 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s39) Pr10.s39) Qr10.s39)
#bm_bool CFSG.KC.BM.CTIB rkr10_40 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s40) Pr10.s40) Qr10.s40)
#bm_bool CFSG.KC.BM.CTIB rkr10_41 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s41) Pr10.s41) Qr10.s41)
#bm_bool CFSG.KC.BM.CTIB rkr10_42 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s42) Pr10.s42) Qr10.s42)
#bm_bool CFSG.KC.BM.CTIB rkr10_43 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s43) Pr10.s43) Qr10.s43)
#bm_bool CFSG.KC.BM.CTIB rkr10_44 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s44) Pr10.s44) Qr10.s44)
#bm_bool CFSG.KC.BM.CTIB rkr10_45 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s45) Pr10.s45) Qr10.s45)
#bm_bool CFSG.KC.BM.CTIB rkr10_46 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s46) Pr10.s46) Qr10.s46)
#bm_bool CFSG.KC.BM.CTIB rkr10_47 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s47) Pr10.s47) Qr10.s47)
#bm_bool CFSG.KC.BM.CTIB rkr10_48 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s48) Pr10.s48) Qr10.s48)
#bm_bool CFSG.KC.BM.CTIB rkr10_49 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s49) Pr10.s49) Qr10.s49)
#bm_bool CFSG.KC.BM.CTIB rkr10_50 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s50) Pr10.s50) Qr10.s50)
#bm_bool CFSG.KC.BM.CTIB rkr10_51 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s51) Pr10.s51) Qr10.s51)
#bm_bool CFSG.KC.BM.CTIB rkr10_52 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s52) Pr10.s52) Qr10.s52)
#bm_bool CFSG.KC.BM.CTIB rkr10_53 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s53) Pr10.s53) Qr10.s53)
#bm_bool CFSG.KC.BM.CTIB rkr10_54 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s54) Pr10.s54) Qr10.s54)
#bm_bool CFSG.KC.BM.CTIB rkr10_55 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s55) Pr10.s55) Qr10.s55)
#bm_bool CFSG.KC.BM.CTIB rkr10_56 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s56) Pr10.s56) Qr10.s56)
#bm_bool CFSG.KC.BM.CTIB rkr10_57 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s57) Pr10.s57) Qr10.s57)
#bm_bool CFSG.KC.BM.CTIB rkr10_58 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s58) Pr10.s58) Qr10.s58)
#bm_bool CFSG.KC.BM.CTIB rkr10_59 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s59) Pr10.s59) Qr10.s59)
#bm_bool CFSG.KC.BM.CTIB rkr10_60 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s60) Pr10.s60) Qr10.s60)
#bm_bool CFSG.KC.BM.CTIB rkr10_61 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s61) Pr10.s61) Qr10.s61)
#bm_bool CFSG.KC.BM.CTIB rkr10_62 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s62) Pr10.s62) Qr10.s62)
#bm_bool CFSG.KC.BM.CTIB rkr10_63 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s63) Pr10.s63) Qr10.s63)
#bm_bool CFSG.KC.BM.CTIB rkr10_64 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s64) Pr10.s64) Qr10.s64)
#bm_bool CFSG.KC.BM.CTIB rkr10_65 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s65) Pr10.s65) Qr10.s65)
#bm_bool CFSG.KC.BM.CTIB rkr10_66 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s66) Pr10.s66) Qr10.s66)
#bm_bool CFSG.KC.BM.CTIB rkr10_67 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s67) Pr10.s67) Qr10.s67)
#bm_bool CFSG.KC.BM.CTIB rkr10_68 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS R10 Pr10.s68) Pr10.s68) Qr10.s68)
#bm_bool CFSG.KC.BM.CTIB wf_Pr10 (CFSG.KC.BM.wfMat Pr10)
#bm_bool CFSG.KC.BM.CTIB wf_Qr10 (CFSG.KC.BM.wfMat Qr10)
#bm_bool CFSG.KC.BM.CTIB shaper10 (CFSG.KC.BM.shapeOK Qr10 2168)
#bm_bool CFSG.KC.BM.CTIB echr10 (CFSG.KC.BM.echFrom Pr10 2168)
