module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f9P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_9_P.bin" 80 9398396774836731489
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f9I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_9_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f10P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_10_P.bin" 160 4032969955035157128
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f10I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_10_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_11_P.bin" 100 15043085182553763290
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_11_I.bin" 24 18071196465248287378
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f12P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_12_P.bin" 105 14537337650702462992
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f12I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_12_I.bin" 15 12172857117205542022
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f13P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_13_P.bin" 875 18065606999014129710
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f13I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_13_I.bin" 125 16276609216193875613
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_14_P.bin" 620 7527167603538769581
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_14_I.bin" 155 9870193615122896760
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f15P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_15_P.bin" 161 7503739173295139104
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f15I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_15_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f16P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_16_P.bin" 163 15849363414250322050
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f16I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_16_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f17P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_17_P.bin" 5672 10793706631412076522
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_92.f17I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_92_17_I.bin" 2810 6517542530349848014

namespace CFSG.KD.ThM3.Rows_M3_92

@[expose] noncomputable def f9 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f9P (2 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f9P (2 * g
    + 1)))) CFSG.KD.ThS.ONE

@[expose] noncomputable def f10 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f10P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f10P (4 *
    g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f10P (4 * g + 2))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f10P (4 *
    g + 3))))

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f11P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f11P (4 *
    g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f11P (4 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f11P (4 * g + 3)))) CFSG.KD.ThS.ONE)

@[expose] noncomputable def f12 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f12P (7 *
    g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 3)))) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 4)))
    (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 5)) (CFSG.KD.ThM3.Rows_M3_92.f12P (7 * g + 6))))

@[expose] noncomputable def f13 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f13P (7 *
    g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 3)))) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 4)))
    (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 5)) (CFSG.KD.ThM3.Rows_M3_92.f13P (7 * g + 6))))

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f14P (4 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f14P (4 *
    g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f14P (4 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f14P (4 * g + 3)))) CFSG.KD.ThS.ONE)

@[expose] noncomputable def f15 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f15P (4 * g + 0))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f15P (4 * g + 1)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f15P (4 *
    g + 2)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f15P (4 * g + 3)))

@[expose] noncomputable def f16 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f16P (4 * g + 0))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f16P (4 * g + 1)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f16P (4 *
    g + 2)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f16P (4 * g + 3)))

@[expose] noncomputable def f17 (g : Nat) : Bool :=
  Nat.blt (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_92.f17P (2 * g + 0))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_92.f17P (2 * g + 1)))

end CFSG.KD.ThM3.Rows_M3_92

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f9 8 as CFSG.KD.ThM3.qq names CFSG.KD.ThM3.Rows_M3_92.f9I
  eval CFSG.KD.ThM3.Rows_M3_92.f9P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f10 8 as CFSG.KD.ThM3.zq names CFSG.KD.ThM3.Rows_M3_92.f10I
  eval CFSG.KD.ThM3.Rows_M3_92.f10P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f11 5 as CFSG.KD.ThM3.qc0 names CFSG.KD.ThM3.Rows_M3_92.f11I
  eval CFSG.KD.ThM3.Rows_M3_92.f11P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f12 3 as CFSG.KD.ThM3.qc0 names CFSG.KD.ThM3.Rows_M3_92.f12I
  eval CFSG.KD.ThM3.Rows_M3_92.f12P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f13 25 as CFSG.KD.ThM3.qc names CFSG.KD.ThM3.Rows_M3_92.f13I
  eval CFSG.KD.ThM3.Rows_M3_92.f13P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f14 31 as CFSG.KD.ThM3.qc names CFSG.KD.ThM3.Rows_M3_92.f14I
  eval CFSG.KD.ThM3.Rows_M3_92.f14P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f15 8 as CFSG.KD.ThM3.xq names CFSG.KD.ThM3.Rows_M3_92.f15I
  eval CFSG.KD.ThM3.Rows_M3_92.f15P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f16 8 as CFSG.KD.ThM3.yq names CFSG.KD.ThM3.Rows_M3_92.f16I
  eval CFSG.KD.ThM3.Rows_M3_92.f16P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_92.f17 511 as CFSG.KD.ThM3.nd names
  CFSG.KD.ThM3.Rows_M3_92.f17I eval CFSG.KD.ThM3.Rows_M3_92.f17P

theorem CFSG.KD.ThM3.t8 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 5)) (nat_lit 3) (nat_lit 2)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.s8 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 11)) (nat_lit 19) (nat_lit 5)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.xx : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 13))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.y6 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 14)) (nat_lit 6) (nat_lit 3)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.za : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 16)) CFSG.KD.ThSeed.SA = true := by
  quickRfl

theorem CFSG.KD.ThM3.z1 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThM3.RB (nat_lit 16))
    CFSG.KD.ThS.ONE) = true := by
  quickRfl

theorem CFSG.KD.ThM3.zz : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 16)) (CFSG.KD.ThM3.RB (nat_lit 16))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.zx : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 16)) (CFSG.KD.ThM3.RB (nat_lit 13))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.zy : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (nat_lit 16)) (CFSG.KD.ThM3.RB (nat_lit 14))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 16))) = true := by
  quickRfl

end
