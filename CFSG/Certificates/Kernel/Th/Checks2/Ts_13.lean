
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

#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_6_P.bin" 228 4797348743131883019
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f6L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_6_L0.bin" 3704 7567382960467049291
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f6O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_6_O0.bin" 19 14667893835390355763
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_6_I.bin" 14 12864564876288800951
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f7P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_7_P.bin" 44 11318700937068152616
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f8P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_8_P.bin" 39 17021675351604551520
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f8I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_8_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f9P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_9_P.bin" 139 231997811645737884
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f9L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_9_L0.bin" 195 904637954755593786
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f9O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_9_O0.bin" 29 2122559981154761890
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f9I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_9_I.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f10P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_10_P.bin" 89 14322284166727366172
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f10L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_10_L0.bin" 195 904637954755593786
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f10O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_10_O0.bin" 29 2122559981154761890
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f10I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_10_I.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_11_P.bin" 89 14322284166727366172
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f11L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_11_L0.bin" 195 904637954755593786
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f11O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_11_O0.bin" 29 2122559981154761890
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_11_I.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f19P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_19_P.bin" 262 15032869711186801908
#kc_repo #kc_items_root CFSG.KD.ThTs.Rows_Ts_13.f20P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ts_13_20_P.bin" 262 8632788807552616927

namespace CFSG.KD.ThTs.Rows_Ts_13

@[expose] noncomputable def f6l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThTs.Rows_Ts_13.f6L0 (CFSG.KD.ThTs.Rows_Ts_13.f6O0 (g + 1) -
    CFSG.KD.ThTs.Rows_Ts_13.f6O0 g) (CFSG.KD.ThTs.Rows_Ts_13.f6O0 g)

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThTs.ROWS (CFSG.KD.ThTs.Rows_Ts_13.f6P (4 * g + 0))
    (CFSG.KD.ThTs.Rows_Ts_13.f6P (4 * g + 1)) (CFSG.KD.ThTs.Rows_Ts_13.f6l0 g)
    (CFSG.KD.ThTs.Rows_Ts_13.f6P (4 * g + 2))) (CFSG.KD.ThTs.Rows_Ts_13.f6P (4 * g + 3))

@[expose] noncomputable def f7 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThTs.Rows_Ts_13.f7P (2 * g + 0)))
    (CFSG.KD.ThTs.Rows_Ts_13.f7P (2 * g + 1))

@[expose] noncomputable def f8 (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.ThTs.ROWS (CFSG.KD.ThTs.Rows_Ts_13.f8P (2 * g + 0))) (CFSG.KD.ThTs.Rows_Ts_13.f8P
    (2 * g + 1))

@[expose] noncomputable def f9l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThTs.Rows_Ts_13.f9L0 (CFSG.KD.ThTs.Rows_Ts_13.f9O0 (g + 1) -
    CFSG.KD.ThTs.Rows_Ts_13.f9O0 g) (CFSG.KD.ThTs.Rows_Ts_13.f9O0 g)

@[expose] noncomputable def f9 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.TsS.runItems (CFSG.KC.Th.TsS.permOK CFSG.KD.ThTs.ROWS CFSG.KD.ThTs.PX
    CFSG.KD.ThTs.PY CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f9P (5 * g + 0)))
    (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f9P (5 * g + 1))) (CFSG.KD.ThTs.Rows_Ts_13.f9P (5 * g
    + 2))) (CFSG.KD.ThTs.Rows_Ts_13.f9l0 g) (CFSG.KD.ThTs.Rows_Ts_13.f9P (5 * g + 3)))
    (CFSG.KD.ThTs.Rows_Ts_13.f9P (5 * g + 4))

@[expose] noncomputable def f10l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThTs.Rows_Ts_13.f10L0 (CFSG.KD.ThTs.Rows_Ts_13.f10O0 (g + 1) -
    CFSG.KD.ThTs.Rows_Ts_13.f10O0 g) (CFSG.KD.ThTs.Rows_Ts_13.f10O0 g)

@[expose] noncomputable def f10 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.TsS.runItems (CFSG.KC.Th.TsS.invOK CFSG.KD.ThTs.TP CFSG.KD.ThTs.INV
    (CFSG.KD.ThTs.Rows_Ts_13.f10P (3 * g + 0))) (CFSG.KD.ThTs.Rows_Ts_13.f10l0 g)
    (CFSG.KD.ThTs.Rows_Ts_13.f10P (3 * g + 1))) (CFSG.KD.ThTs.Rows_Ts_13.f10P (3 * g + 2))

@[expose] noncomputable def f11l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThTs.Rows_Ts_13.f11L0 (CFSG.KD.ThTs.Rows_Ts_13.f11O0 (g + 1) -
    CFSG.KD.ThTs.Rows_Ts_13.f11O0 g) (CFSG.KD.ThTs.Rows_Ts_13.f11O0 g)

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.TsS.runItems (CFSG.KC.Th.TsS.treeOK CFSG.KD.ThTs.TP CFSG.KD.ThTs.TPA
    CFSG.KD.ThTs.TLA CFSG.KD.ThTs.PX CFSG.KD.ThTs.PY (CFSG.KD.ThTs.Rows_Ts_13.f11P (3 * g + 0)))
    (CFSG.KD.ThTs.Rows_Ts_13.f11l0 g) (CFSG.KD.ThTs.Rows_Ts_13.f11P (3 * g + 1)))
    (CFSG.KD.ThTs.Rows_Ts_13.f11P (3 * g + 2))

@[expose] noncomputable def f19 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.canon2 (CFSG.KC.Th.vecB CFSG.KD.ThS.rm (Nat.land (CFSG.KC.Th.canon2
    (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 0)) (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 1)))
    (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 2))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f19P (10
    * g + 3)))) (CFSG.KC.Th.vecB CFSG.KD.ThS.rm (Nat.shiftRight (CFSG.KC.Th.canon2
    (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 4)) (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 5)))
    (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 6))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f19P (10
    * g + 7))))) (CFSG.KC.Th.canon2 (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 8))
    (CFSG.KD.ThTs.Rows_Ts_13.f19P (10 * g + 9)))

@[expose] noncomputable def f20 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.canon2 (CFSG.KC.Th.vecB CFSG.KD.ThS.rm (Nat.land (CFSG.KC.Th.canon2
    (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 0)) (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 1)))
    (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 2))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f20P (10
    * g + 3)))) (CFSG.KC.Th.vecB CFSG.KD.ThS.rm (Nat.shiftRight (CFSG.KC.Th.canon2
    (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 4)) (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 5)))
    (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 6))) (CFSG.KD.ThTs.RB (CFSG.KD.ThTs.Rows_Ts_13.f20P (10
    * g + 7))))) (CFSG.KC.Th.canon2 (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 8))
    (CFSG.KD.ThTs.Rows_Ts_13.f20P (10 * g + 9)))

end CFSG.KD.ThTs.Rows_Ts_13

#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_13.f6 3 as CFSG.KD.ThTs.sr names CFSG.KD.ThTs.Rows_Ts_13.f6I
  eval CFSG.KD.ThTs.Rows_Ts_13.f6P CFSG.KD.ThTs.Rows_Ts_13.f6l0
#kc_unfold CFSG.KD.ThTs.srn CFSG.KD.ThTs.Rows_Ts_13.f7 0 eval CFSG.KD.ThTs.Rows_Ts_13.f7P
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_13.f8 1 as CFSG.KD.ThTs.row names CFSG.KD.ThTs.Rows_Ts_13.f8I
  eval CFSG.KD.ThTs.Rows_Ts_13.f8P
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_13.f9 5 as CFSG.KD.ThTs.pm names CFSG.KD.ThTs.Rows_Ts_13.f9I
  eval CFSG.KD.ThTs.Rows_Ts_13.f9P CFSG.KD.ThTs.Rows_Ts_13.f9l0
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_13.f10 5 as CFSG.KD.ThTs.iv names CFSG.KD.ThTs.Rows_Ts_13.f10I
  eval CFSG.KD.ThTs.Rows_Ts_13.f10P CFSG.KD.ThTs.Rows_Ts_13.f10l0
#kc_rows_unfold CFSG.KD.ThTs.Rows_Ts_13.f11 5 as CFSG.KD.ThTs.tr names CFSG.KD.ThTs.Rows_Ts_13.f11I
  eval CFSG.KD.ThTs.Rows_Ts_13.f11P CFSG.KD.ThTs.Rows_Ts_13.f11l0
#kc_unfold CFSG.KD.ThTs.kx CFSG.KD.ThTs.Rows_Ts_13.f19 0 eval CFSG.KD.ThTs.Rows_Ts_13.f19P
#kc_unfold CFSG.KD.ThTs.ky CFSG.KD.ThTs.Rows_Ts_13.f20 0 eval CFSG.KD.ThTs.Rows_Ts_13.f20P

theorem CFSG.KD.ThTs.pLrows : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.ROWS (nat_lit 2457) true
    CFSG.KD.ThTs.Lrows = true := by
  quickRfl

theorem CFSG.KD.ThTs.pLpx : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.PX (nat_lit 2457) false
    CFSG.KD.ThTs.Lpx = true := by
  quickRfl

theorem CFSG.KD.ThTs.pLpy : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.PY (nat_lit 2457) false
    CFSG.KD.ThTs.Lpy = true := by
  quickRfl

theorem CFSG.KD.ThTs.pLtp : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.TP (nat_lit 2457) false
    CFSG.KD.ThTs.Ltp = true := by
  quickRfl

theorem CFSG.KD.ThTs.pLtpa : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.TPA (nat_lit 2457) false
    CFSG.KD.ThTs.Ltpa = true := by
  quickRfl

theorem CFSG.KD.ThTs.pLtla : CFSG.KC.Th.TsS.natsRun CFSG.KD.ThTs.TLA (nat_lit 2457) false
    CFSG.KD.ThTs.Ltla = true := by
  quickRfl

theorem CFSG.KD.ThTs.tp0 : Nat.beq (CFSG.KD.ThTs.TP (nat_lit 0)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThTs.xx : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 1)) (CFSG.KD.ThTs.RB (nat_lit 1))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThTs.x1 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThTs.RB (nat_lit 1))
    CFSG.KD.ThS.ONE) = true := by
  quickRfl

theorem CFSG.KD.ThTs.yyy : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KC.Th.mulB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 2)) (CFSG.KD.ThTs.RB (nat_lit 2)))
    (CFSG.KD.ThTs.RB (nat_lit 2))) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThTs.y1 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KD.ThTs.RB (nat_lit 2))
    CFSG.KD.ThS.ONE) = true := by
  quickRfl

theorem CFSG.KD.ThTs.xy21 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB (nat_lit 1))
    (CFSG.KD.ThTs.RB (nat_lit 2))) (nat_lit 21) (nat_lit 5)) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThTs.xy3 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 1)) (CFSG.KD.ThTs.RB (nat_lit 2))) (nat_lit 3) (nat_lit 2)) CFSG.KD.ThS.ONE) = true :=
    by
  quickRfl

theorem CFSG.KD.ThTs.xy7 : CFSG.KC.Th.BigS.notB (Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThTs.RB
    (nat_lit 1)) (CFSG.KD.ThTs.RB (nat_lit 2))) (nat_lit 7) (nat_lit 3)) CFSG.KD.ThS.ONE) = true :=
    by
  quickRfl

end
