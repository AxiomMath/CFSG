
module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.TsS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.M3_const
public import CFSG.Certificates.Kernel.Th.S.Data.Ts_const
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_2_P.bin" 47 4316860503771176349
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_14_P.bin" 80 16108787186530764132
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_R.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_R_14_I.bin" 40 348359025702806052

namespace CFSG.KD.ThTs.Rows_Ts_R

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 0))) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 1))) (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g +
    2)) (CFSG.KD.ThTs.Rows_Ts_R.f2P (4 * g + 3)))

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (CFSG.KD.ThTs.Rows_Ts_R.f14P (2 * g + 0))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_R.f14P (2 * g
    + 1)))) CFSG.KD.ThS.ONE

end CFSG.KD.ThTs.Rows_Ts_R

#kc_unfold CFSG.KD.ThTs.rLY CFSG.KD.ThTs.Rows_Ts_R.f2 0 eval CFSG.KD.ThTs.Rows_Ts_R.f2P
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_R.f14 8 as CFSG.KD.ThTs.rIE names CFSG.KD.ThTs.Rows_Ts_R.f14I
  eval CFSG.KD.ThTs.Rows_Ts_R.f14P

theorem CFSG.KD.ThTs.rBB : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 0)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThSeed.SB CFSG.KD.ThSeed.SB) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rLX : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (nat_lit 0)) (nat_lit 19676527007948218914) (nat_lit 33)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rLY2 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 3)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 2))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rC0 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 4)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KD.ThTs.RB
    (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 3)) (nat_lit 71641224) (nat_lit 15)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rC1 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 5)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KD.ThTs.RB
    (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 3)) (nat_lit 74159786122) (nat_lit 20)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rK : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 6)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KD.ThTs.RB
    (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 3)) (nat_lit 69) (nat_lit 4)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rKi : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 7)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThTs.RB (nat_lit 1)) (CFSG.KD.ThTs.RB
    (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 3)) (nat_lit 162) (nat_lit 4)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE2 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 8)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 6))
    (CFSG.KD.ThTs.RB (nat_lit 4))) (CFSG.KD.ThTs.RB (nat_lit 7))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE3 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 9)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 6))
    (CFSG.KD.ThTs.RB (nat_lit 5))) (CFSG.KD.ThTs.RB (nat_lit 7))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE4 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 11)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 4))
    (CFSG.KD.ThTs.RB (nat_lit 10))) (CFSG.KD.ThTs.RB (nat_lit 8))) (CFSG.KD.ThTs.RB (nat_lit 9)))
    (CFSG.KD.ThTs.RB (nat_lit 4))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE5 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 13)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 12))
    (CFSG.KD.ThTs.RB (nat_lit 12))) (CFSG.KD.ThTs.RB (nat_lit 4))) (CFSG.KD.ThTs.RB (nat_lit 5)))
    (CFSG.KD.ThTs.RB (nat_lit 5))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE6 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 14)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 13))
    (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11)))
    (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13)))
    (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11)))
    (CFSG.KD.ThTs.RB (nat_lit 13))) (CFSG.KD.ThTs.RB (nat_lit 11))) (CFSG.KD.ThTs.RB (nat_lit 13)))
    = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE7 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 15)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 12)) (CFSG.KD.ThTs.RB (nat_lit 12))) (CFSG.KD.ThTs.RB
    (nat_lit 8))) (CFSG.KD.ThTs.RB (nat_lit 4))) (CFSG.KD.ThTs.RB (nat_lit 9))) (CFSG.KD.ThTs.RB
    (nat_lit 5))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE8 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 16)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 15)) (CFSG.KD.ThTs.RB (nat_lit 15))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE9 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 18)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 14))
    (CFSG.KD.ThTs.RB (nat_lit 17))) (CFSG.KD.ThTs.RB (nat_lit 17))) (CFSG.KD.ThTs.RB (nat_lit 14)))
    (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB (nat_lit 14)))
    (CFSG.KD.ThTs.RB (nat_lit 16))) (CFSG.KD.ThTs.RB (nat_lit 14))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rIC0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 4)) (CFSG.KD.ThTs.RB (nat_lit 19))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThTs.rIC1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 5)) (CFSG.KD.ThTs.RB (nat_lit 12))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThTs.rV : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 26)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (nat_lit 0)) (nat_lit 373911662824283980869) (nat_lit 35)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rVi : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 27)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThSeed.SA CFSG.KD.ThSeed.SB
    (CFSG.KD.ThTs.RB (nat_lit 0)) (nat_lit 747708476841837865098) (nat_lit 35)) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rTt : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 28)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 27))
    CFSG.KD.ThSeed.SA) (CFSG.KD.ThTs.RB (nat_lit 26))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rTG : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 29)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 26))
    (CFSG.KD.ThTs.RB (nat_lit 6))) (CFSG.KD.ThTs.RB (nat_lit 27))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rTGi : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 30)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 26))
    (CFSG.KD.ThTs.RB (nat_lit 7))) (CFSG.KD.ThTs.RB (nat_lit 27))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rTR : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 31)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 29))
    CFSG.KD.ThSeed.SA) (CFSG.KD.ThTs.RB (nat_lit 30))) = true := by
  quickRfl

theorem CFSG.KD.ThTs.rE217 : Nat.beq (CFSG.KD.ThTs.RB (nat_lit 32)) (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB
    (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 15)) (nat_lit 1352160579797152663358438253090) (nat_lit
    52)) (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB
    (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 15)) (nat_lit 85004562)
    (nat_lit 14))) (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB (nat_lit 15))
    (nat_lit 340018248) (nat_lit 16))) (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14)) (CFSG.KD.ThM3.RB
    (nat_lit 15)) (nat_lit 18539942178) (nat_lit 18))) (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThM3.RB (nat_lit 13)) (CFSG.KD.ThM3.RB (nat_lit 14))
    (CFSG.KD.ThM3.RB (nat_lit 15)) (nat_lit 5655040296) (nat_lit 18))) = true := by
  quickRfl

end
