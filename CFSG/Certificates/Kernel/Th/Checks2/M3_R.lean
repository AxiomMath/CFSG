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

#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_6_P.bin" 44 8702089246535798533
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_6_I.bin" 15 5512800217539681965
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_14_P.bin" 329 3041409730081082928
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_14_I.bin" 39 18362343629704035864
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f17P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_17_P.bin" 7956 17412235879230179726
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f17I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_17_I.bin" 2806 3057087102027320484
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f18P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_18_P.bin" 251 12125586827065694877
#kc_repo #kc_items_root CFSG.KD.ThM3.Rows_M3_R.f18I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/M3_R_18_I.bin" 35 3525205344064885652

namespace CFSG.KD.ThM3.Rows_M3_R

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 0))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 1))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f6P (3 * g + 2))))

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 0))) (CFSG.KC.Th.BigS.powB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 1)))
    (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 3))) (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 4))
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 5))) (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 6))
    (CFSG.KD.ThM3.Rows_M3_R.f14P (8 * g + 7)))

@[expose] noncomputable def f17 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 0))) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 1))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f17P (3 * g + 2))))

@[expose] noncomputable def f18 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 0))) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 *
    g + 1))) (CFSG.KD.ThM3.RB (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 2))) (CFSG.KD.ThM3.RB
    (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 3))) (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 4))
    (CFSG.KD.ThM3.Rows_M3_R.f18P (6 * g + 5)))

end CFSG.KD.ThM3.Rows_M3_R

#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f6 3 as CFSG.KD.ThM3.rS names CFSG.KD.ThM3.Rows_M3_R.f6I eval
  CFSG.KD.ThM3.Rows_M3_R.f6P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f14 8 as CFSG.KD.ThM3.rQ names CFSG.KD.ThM3.Rows_M3_R.f14I
  eval CFSG.KD.ThM3.Rows_M3_R.f14P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f17 510 as CFSG.KD.ThM3.rNF names CFSG.KD.ThM3.Rows_M3_R.f17I
  eval CFSG.KD.ThM3.Rows_M3_R.f17P
#kc_rows_unfold CFSG.KD.ThM3.Rows_M3_R.f18 7 as CFSG.KD.ThM3.rC names CFSG.KD.ThM3.Rows_M3_R.f18I
  eval CFSG.KD.ThM3.Rows_M3_R.f18P

theorem CFSG.KD.ThM3.rT3 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 0)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rT4 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 1)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 0)) CFSG.KD.ThSeed.SB) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rT5 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 2)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 0)) (CFSG.KD.ThM3.RB (nat_lit 1))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rT6 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 3)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 0)) (CFSG.KD.ThM3.RB (nat_lit 2))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rT7 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 4)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThSeed.SA (CFSG.KD.ThM3.RB (nat_lit 3))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rT8 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 5)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 3)) CFSG.KD.ThSeed.SA) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rU : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 6)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 5)) (nat_lit 2) (nat_lit 2)) (CFSG.KD.ThM3.RB (nat_lit 4))) = true :=
    by
  quickRfl

theorem CFSG.KD.ThM3.rS7 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 10)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThSeed.SA (CFSG.KD.ThM3.RB (nat_lit 9))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rS8p : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 11)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 9)) CFSG.KD.ThSeed.SA) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rV : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 12)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 11)) (nat_lit 18) (nat_lit 5)) (CFSG.KD.ThM3.RB (nat_lit 10))) = true
    := by
  quickRfl

theorem CFSG.KD.ThM3.rX : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 12)) (nat_lit 14) (nat_lit 4)) = true
    := by
  quickRfl

theorem CFSG.KD.ThM3.rY : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 4)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 6)) (nat_lit 9) (nat_lit 4))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rY5 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 15)) (CFSG.KC.Th.BigS.powB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 14)) (nat_lit 5) (nat_lit
    3)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rZ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 16)) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 84) (nat_lit 4)) (nat_lit 9) (nat_lit 4)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rNF0 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 25)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThM3.rNF1 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 26)) (CFSG.KD.ThM3.RB (nat_lit 16)) =
    true := by
  quickRfl

theorem CFSG.KD.ThM3.rWA : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 544)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 537))
    (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit
    538)) (nat_lit 2) (nat_lit 2))) (CFSG.KD.ThM3.RB (nat_lit 537))) (CFSG.KD.ThM3.RB (nat_lit
    539))) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB
    (nat_lit 540)) (nat_lit 2) (nat_lit 2))) (CFSG.KD.ThM3.RB (nat_lit 539))) (CFSG.KD.ThM3.RB
    (nat_lit 541))) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 542)) (nat_lit 2) (nat_lit 2))) (CFSG.KD.ThM3.RB (nat_lit 541))) =
    true := by
  quickRfl

theorem CFSG.KD.ThM3.rWB : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 545)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 537)) (nat_lit 2) (nat_lit 2)) (CFSG.KD.ThM3.RB (nat_lit 538)))
    (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit
    539)) (nat_lit 2) (nat_lit 2))) (CFSG.KD.ThM3.RB (nat_lit 538))) (CFSG.KC.Th.BigS.powB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 540)) (nat_lit 2)
    (nat_lit 2))) (CFSG.KD.ThM3.RB (nat_lit 541))) (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 542)) (nat_lit 2) (nat_lit 2)))
    (CFSG.KD.ThM3.RB (nat_lit 543))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rCXQ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 546)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 18))) (CFSG.KD.ThM3.RB
    (nat_lit 13))) (CFSG.KD.ThM3.RB (nat_lit 18))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rD : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 547)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB
    (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 15)) (nat_lit 5986089550763093) (nat_lit 27)) = true :=
    by
  quickRfl

theorem CFSG.KD.ThM3.rGFQ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 548)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB CFSG.KD.ThS.ONE
    (nat_lit 276) (nat_lit 5)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rGiFQ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 549)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB CFSG.KD.ThS.ONE
    (nat_lit 5445) (nat_lit 8)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rFQ : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 550)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 549)) (CFSG.KD.ThM3.RB
    (nat_lit 17))) (CFSG.KD.ThM3.RB (nat_lit 548))) CFSG.KD.ThSeed.SA) (nat_lit 9) (nat_lit 4))
    (CFSG.KD.ThM3.RB (nat_lit 549))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rGFX : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 551)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB CFSG.KD.ThS.ONE
    (nat_lit 17896517) (nat_lit 13)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rGiFX : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 552)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB CFSG.KD.ThS.ONE
    (nat_lit 1461653360965) (nat_lit 21)) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rFX : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 553)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 552)) (CFSG.KD.ThM3.RB
    (nat_lit 13))) (CFSG.KD.ThM3.RB (nat_lit 551))) CFSG.KD.ThSeed.SA) (nat_lit 9) (nat_lit 4))
    (CFSG.KD.ThM3.RB (nat_lit 552))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rE1 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 554)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 18)) (CFSG.KD.ThM3.RB (nat_lit 19))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rE2 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 555)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 18)) (CFSG.KD.ThM3.RB (nat_lit 22))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rF0 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 556)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 18))
    (CFSG.KD.ThM3.RB (nat_lit 20))) (CFSG.KD.ThM3.RB (nat_lit 21))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rF2 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 557)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 20)) (CFSG.KD.ThM3.RB (nat_lit 23))) = true := by
  quickRfl

theorem CFSG.KD.ThM3.rF3 : Nat.beq (CFSG.KD.ThM3.RB (nat_lit 558)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThM3.RB (nat_lit 20)) (CFSG.KD.ThM3.RB (nat_lit 21))) = true := by
  quickRfl

end
