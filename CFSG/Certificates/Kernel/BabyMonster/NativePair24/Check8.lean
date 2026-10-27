module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.F2
public import CFSG.Certificates.Kernel.BabyMonster.Render
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data3
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data4
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data5
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Vecs

#bm_mul CFSG.KC.BM.NativePair24 conjF W [F] F0 [W]
#bm_mul CFSG.KC.BM.NativePair24 f0sq F0 [F0] I []
#bm_bool CFSG.KC.BM.NativePair24 ne_F0 (CFSG.KC.BM.notB (CFSG.KC.BM.isId F0))
#bm_bool CFSG.KC.BM.NativePair24 rkF0_0 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s0) PF0.s0) QF0.s0)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_1 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s1) PF0.s1) QF0.s1)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_2 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s2) PF0.s2) QF0.s2)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_3 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s3) PF0.s3) QF0.s3)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_4 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s4) PF0.s4) QF0.s4)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_5 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s5) PF0.s5) QF0.s5)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_6 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s6) PF0.s6) QF0.s6)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_7 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s7) PF0.s7) QF0.s7)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_8 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s8) PF0.s8) QF0.s8)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_9 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s9) PF0.s9) QF0.s9)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_10 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s10) PF0.s10) QF0.s10)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_11 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s11) PF0.s11) QF0.s11)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_12 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s12) PF0.s12) QF0.s12)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_13 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s13) PF0.s13) QF0.s13)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_14 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s14) PF0.s14) QF0.s14)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_15 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s15) PF0.s15) QF0.s15)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_16 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s16) PF0.s16) QF0.s16)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_17 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s17) PF0.s17) QF0.s17)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_18 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s18) PF0.s18) QF0.s18)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_19 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s19) PF0.s19) QF0.s19)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_20 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s20) PF0.s20) QF0.s20)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_21 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s21) PF0.s21) QF0.s21)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_22 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s22) PF0.s22) QF0.s22)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_23 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s23) PF0.s23) QF0.s23)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_24 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s24) PF0.s24) QF0.s24)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_25 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s25) PF0.s25) QF0.s25)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_26 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s26) PF0.s26) QF0.s26)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_27 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s27) PF0.s27) QF0.s27)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_28 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s28) PF0.s28) QF0.s28)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_29 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s29) PF0.s29) QF0.s29)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_30 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s30) PF0.s30) QF0.s30)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_31 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s31) PF0.s31) QF0.s31)
#bm_bool CFSG.KC.BM.NativePair24 rkF0_32 (Nat.beq (Nat.xor (CFSG.KC.BM.mulS F0 PF0.s32) PF0.s32) QF0.s32)
