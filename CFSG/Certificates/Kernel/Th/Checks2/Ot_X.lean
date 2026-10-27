module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.Data.Ot_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_X.f1P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_X_1_P.bin" 389 6560041783063326664
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_X.f1I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_X_1_I.bin" 106 5643385604707033596
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_X.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_X_2_P.bin" 149 12292855764968934959
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_X.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_X_2_I.bin" 40 16109616377093704663

namespace CFSG.KD.ThO.Rows_Ot_X

@[expose] noncomputable def f1 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E1 (CFSG.KD.ThO.Rows_Ot_X.f1P (4 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_X.f1P (4 * g + 1)) (CFSG.KD.ThO.Rows_Ot_X.f1P (4 * g + 2)))
    (CFSG.KD.ThO.Rows_Ot_X.f1P (4 * g + 3))

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E2 (CFSG.KD.ThO.Rows_Ot_X.f2P (4 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_X.f2P (4 * g + 1)) (CFSG.KD.ThO.Rows_Ot_X.f2P (4 * g + 2)))
    (CFSG.KD.ThO.Rows_Ot_X.f2P (4 * g + 3))

end CFSG.KD.ThO.Rows_Ot_X

#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_X.f1 18 as CFSG.KD.ThO.c1_ names CFSG.KD.ThO.Rows_Ot_X.f1I eval
  CFSG.KD.ThO.Rows_Ot_X.f1P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_X.f2 7 as CFSG.KD.ThO.c2_ names CFSG.KD.ThO.Rows_Ot_X.f2I eval
  CFSG.KD.ThO.Rows_Ot_X.f2P

theorem CFSG.KD.ThO.ra : CFSG.KC.Th.OutS.invRank (nat_lit 6) (CFSG.KC.Th.DceS.let24 CFSG.KD.ThB.LT
    (nat_lit 0)) = true := by
  quickRfl

theorem CFSG.KD.ThO.c3_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E3 (nat_lit 0) (nat_lit 486)
    (nat_lit 8)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c4_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E4 (nat_lit 0) (nat_lit 288)
    (nat_lit 5)) (nat_lit 3) = true := by
  quickRfl

theorem CFSG.KD.ThO.c5_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E5 (nat_lit 0) (nat_lit 54)
    (nat_lit 1)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c6_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E6 (nat_lit 0) (nat_lit 6)
    (nat_lit 1)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c7_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E7 (nat_lit 0) (nat_lit 126)
    (nat_lit 2)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c8_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E8 (nat_lit 0) (nat_lit 78)
    (nat_lit 2)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c9_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E9 (nat_lit 0) (nat_lit 72)
    (nat_lit 2)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c10_0 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E10 (nat_lit 0) (nat_lit
    2048) (nat_lit 32)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.c10_2048 : Nat.beq (CFSG.KC.Th.OutS.countA CFSG.KD.ThB.E10 (nat_lit 2048)
    (nat_lit 1480) (nat_lit 24)) (nat_lit 0) = true := by
  quickRfl

theorem CFSG.KD.ThO.core : CFSG.KC.Th.OutS.coreOK CFSG.KD.ThB.E6 CFSG.KD.ThB.LT CFSG.KD.ThB.LI
    (nat_lit 2) (nat_lit 6) = true := by
  quickRfl

end
