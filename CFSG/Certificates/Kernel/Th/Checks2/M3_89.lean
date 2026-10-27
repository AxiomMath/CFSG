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

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_1_P.bin" 816 7846503857225895475
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_1_I.bin" 175 14408900664528795822
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_2_P.bin" 11826 5234793399416804311
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_2_I.bin" 2815 16331079668357339593
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f4P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_4_P.bin" 17462 8489530204686437900
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f4I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_4_I.bin" 1494 16167401876628029979
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f5P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_5_P.bin" 10130 5744813722535796733
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f5I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_5_I.bin" 2640 6112791218695063942
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_6_P.bin" 2654 8111100517001684408
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_89.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_89_6_I.bin" 1312 10642151775918648353

namespace CFSG.KD.ThM3.Rows_M3_89

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f1P (5 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f1P (5 * g
    + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f1P (5 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f1P (5 * g + 3)))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f1P (5 * g
    + 4))))

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f2P (4 * g + 0)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f2P (4 * g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f2P (4 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f2P (4 * g + 3))))) CFSG.KD.ThS.ONE)

@[expose] noncomputable def f4 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 0)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 1))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 2))) (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 3))
    (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 4))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f4P (12 *
    g + 5)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 6))) (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 7))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 8))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f4P (12 *
    g + 9))) (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g + 10)) (CFSG.KD.ThM3.Rows_M3_89.f4P (12 * g +
    11))))

@[expose] noncomputable def f5 (g : Nat) : Bool :=
  CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f5P (4 * g + 0)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f5P (4 * g + 1)))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f5P (4 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f5P (4 * g + 3))))) CFSG.KD.ThS.ONE)

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_89.f6P (2 * g + 0))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_89.f6P (2 * g
    + 1)))) CFSG.KD.ThS.ONE)

end CFSG.KD.ThM3.Rows_M3_89

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_89.f1 32 as CFSG.KD.ThM3.i2_ names CFSG.KD.ThM3.Rows_M3_89.f1I
  eval CFSG.KD.ThM3.Rows_M3_89.f1P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_89.f2 512 as CFSG.KD.ThM3.i3_ names CFSG.KD.ThM3.Rows_M3_89.f2I
  eval CFSG.KD.ThM3.Rows_M3_89.f2P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_89.f4 270 as CFSG.KD.ThM3.i1_ names CFSG.KD.ThM3.Rows_M3_89.f4I
  eval CFSG.KD.ThM3.Rows_M3_89.f4P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_89.f5 480 as CFSG.KD.ThM3.i2_ names CFSG.KD.ThM3.Rows_M3_89.f5I
  eval CFSG.KD.ThM3.Rows_M3_89.f5P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_89.f6 240 as CFSG.KD.ThM3.i1_ names CFSG.KD.ThM3.Rows_M3_89.f6I
  eval CFSG.KD.ThM3.Rows_M3_89.f6P

theorem CFSG.KD.ThM3.i1_0 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 25)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.i1_1 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 26)) (CFSG.KD.ThM3.RB (nat_lit 16)) =
    true := by
  quickRfl

end
