module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.RowsUnfold

public section

set_option maxRecDepth 100000

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_2_P.bin" 25 6972650108088181448
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f2L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_2_L0.bin" 7 13859946077019414859
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f2O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_2_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_2_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_6_P.bin" 29 11592642380499423193
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f6L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_6_L0.bin" 19 9266222651202518962
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f6O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_6_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_6_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f7P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_7_P.bin" 72 15197102505925800649
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f7L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_7_L0.bin" 15 18418934679390312869
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f7O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_7_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f7I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_7_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f8P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_8_P.bin" 125 17192025678103953097
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f8I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_8_I.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f10P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_10_P.bin" 30 10971279838663765773
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f10L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_10_L0.bin" 19 2583876609026369642
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f10O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_10_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f10I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_10_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_11_P.bin" 73 8303179395162223096
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f11L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_11_L0.bin" 15 16670972015698590049
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f11O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_11_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y7.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y7_11_I.bin" 4 14007230941556241898

namespace CFSG.KD.ThS.Rows_Sm_Y7

@[expose] noncomputable def f2l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y7.f2L0 (CFSG.KD.ThS.Rows_Sm_Y7.f2O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y7.f2O0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f2O0 g)

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runPc CFSG.KD.ThS.RBp7 CFSG.KD.ThS.PW7 CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThS.PR7 (CFSG.KD.ThS.Rows_Sm_Y7.f2P (5 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y7.f2P (5 * g + 1)) (CFSG.KD.ThS.Rows_Sm_Y7.f2P (5 * g + 2))
    (CFSG.KD.ThS.Rows_Sm_Y7.f2l0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f2P (5 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y7.f2P (5 * g + 4))

@[expose] noncomputable def f6l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y7.f6L0 (CFSG.KD.ThS.Rows_Sm_Y7.f6O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y7.f6O0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f6O0 g)

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp7 CFSG.KD.ThS.PT7_0 CFSG.KD.ThS.rm CFSG.KD.ThS.PR7
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7
    (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y7.f6l0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y7.f6P (6 * g + 5))

@[expose] noncomputable def f7l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y7.f7L0 (CFSG.KD.ThS.Rows_Sm_Y7.f7O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y7.f7O0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f7O0 g)

@[expose] noncomputable def f7 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT7_0 (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y7.f7l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y7.f7P (8 * g + 7))

@[expose] noncomputable def f8 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 0))) (Nat.pow
    (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7
    (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 3)))
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y7.f8P (6 * g + 5)))))

@[expose] noncomputable def f10l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y7.f10L0 (CFSG.KD.ThS.Rows_Sm_Y7.f10O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y7.f10O0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f10O0 g)

@[expose] noncomputable def f10 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp7 CFSG.KD.ThS.PT7_1 CFSG.KD.ThS.rm CFSG.KD.ThS.PR7
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7
    (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y7.f10l0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y7.f10P (6 * g + 5))

@[expose] noncomputable def f11l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y7.f11L0 (CFSG.KD.ThS.Rows_Sm_Y7.f11O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y7.f11O0 g) (CFSG.KD.ThS.Rows_Sm_Y7.f11O0 g)

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT7_1 (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y7.f11l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y7.f11P (8 * g + 7))

end CFSG.KD.ThS.Rows_Sm_Y7

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f2 1 as CFSG.KD.ThS.pc7_ names CFSG.KD.ThS.Rows_Sm_Y7.f2I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f2P CFSG.KD.ThS.Rows_Sm_Y7.f2l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f6 1 as CFSG.KD.ThS.bt7_0_ names CFSG.KD.ThS.Rows_Sm_Y7.f6I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f6P CFSG.KD.ThS.Rows_Sm_Y7.f6l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f7 1 as CFSG.KD.ThS.bs7_0_ names CFSG.KD.ThS.Rows_Sm_Y7.f7I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f7P CFSG.KD.ThS.Rows_Sm_Y7.f7l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f8 2 as CFSG.KD.ThS.bn7_ names CFSG.KD.ThS.Rows_Sm_Y7.f8I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f8P
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f10 1 as CFSG.KD.ThS.bt7_1_ names CFSG.KD.ThS.Rows_Sm_Y7.f10I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f10P CFSG.KD.ThS.Rows_Sm_Y7.f10l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y7.f11 1 as CFSG.KD.ThS.bs7_1_ names CFSG.KD.ThS.Rows_Sm_Y7.f11I
  eval CFSG.KD.ThS.Rows_Sm_Y7.f11P CFSG.KD.ThS.Rows_Sm_Y7.f11l0

theorem CFSG.KD.ThS.sd7 : CFSG.KC.Th.andB (Nat.beq (CFSG.KD.ThS.RBp7 (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 1))) (Nat.beq (CFSG.KD.ThS.RBp7 (nat_lit 2)) (CFSG.KD.ThS.RBf (nat_lit 2))) = true :=
    by
  quickRfl

theorem CFSG.KD.ThS.pw7 : CFSG.KC.Th.BigS.pwOK CFSG.KD.ThS.RBp7 CFSG.KD.ThS.PW7 CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.PR7 (nat_lit 2) (nat_lit 7) = true := by
  quickRfl

theorem CFSG.KD.ThS.gpc7 : CFSG.KC.Th.BigS.gensPcOK CFSG.KD.ThS.GL7 (nat_lit 2) CFSG.KD.ThS.PR7
    CFSG.KD.ThS.n7 (nat_lit 32) = true := by
  quickRfl

theorem CFSG.KD.ThS.rg7 : CFSG.KC.Th.andB (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.PR7 CFSG.KD.ThS.n7
    (nat_lit 36)) (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.GL7 (nat_lit 2) (nat_lit 36)) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf7_0 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp7 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR7 (CFSG.KD.ThS.PT7_0 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (nat_lit
    5) (nat_lit 5)) (nat_lit 2) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf7_1 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp7 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR7 (CFSG.KD.ThS.PT7_1 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL7 (nat_lit
    15) (nat_lit 5)) (nat_lit 2) = true := by
  quickRfl

theorem CFSG.KD.ThS.bl7 : CFSG.KC.Th.BigS.blocksOK CFSG.KD.ThS.BL7 CFSG.KD.ThS.nb7 CFSG.KD.ThS.n7 =
    true := by
  quickRfl

end
