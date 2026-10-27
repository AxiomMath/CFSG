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

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f2P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_2_P.bin" 25 13643945044656934315
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f2L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_2_L0.bin" 11 7860433822879778943
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f2O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_2_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f2I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_2_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f6P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_6_P.bin" 29 10937344134144857739
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f6L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_6_L0.bin" 14 4506458681052615227
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f6O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_6_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f6I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_6_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f7P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_7_P.bin" 72 8866377509525610241
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f7L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_7_L0.bin" 12 17698383783521991882
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f7O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_7_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f7I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_7_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f8P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_8_P.bin" 188 13174276992094709108
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f8I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_8_I.bin" 14 12864564876288800951
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f10P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_10_P.bin" 30 10390677446552186280
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f10L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_10_L0.bin" 15 13604442005720887331
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f10O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_10_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f10I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_10_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f11P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_11_P.bin" 73 10435886549164118715
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f11L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_11_L0.bin" 12 16137021718461934455
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f11O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_11_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f11I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_11_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f13P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_13_P.bin" 30 5507747999091686864
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f13L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_13_L0.bin" 15 4248338429471468209
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f13O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_13_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f13I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_13_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f14P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_14_P.bin" 73 11032955529683205219
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f14L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_14_L0.bin" 12 4900876071114527642
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f14O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_14_O0.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_Y5.f14I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_Y5_14_I.bin" 4 14007230941556241898

namespace CFSG.KD.ThS.Rows_Sm_Y5

@[expose] noncomputable def f2l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f2L0 (CFSG.KD.ThS.Rows_Sm_Y5.f2O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f2O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f2O0 g)

@[expose] noncomputable def f2 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runPc CFSG.KD.ThS.RBp5 CFSG.KD.ThS.PW5 CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThS.PR5 (CFSG.KD.ThS.Rows_Sm_Y5.f2P (5 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y5.f2P (5 * g + 1)) (CFSG.KD.ThS.Rows_Sm_Y5.f2P (5 * g + 2))
    (CFSG.KD.ThS.Rows_Sm_Y5.f2l0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f2P (5 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f2P (5 * g + 4))

@[expose] noncomputable def f6l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f6L0 (CFSG.KD.ThS.Rows_Sm_Y5.f6O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f6O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f6O0 g)

@[expose] noncomputable def f6 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp5 CFSG.KD.ThS.PT5_0 CFSG.KD.ThS.rm CFSG.KD.ThS.PR5
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5
    (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f6l0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f6P (6 * g + 5))

@[expose] noncomputable def f7l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f7L0 (CFSG.KD.ThS.Rows_Sm_Y5.f7O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f7O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f7O0 g)

@[expose] noncomputable def f7 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT5_0 (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y5.f7l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y5.f7P (8 * g + 7))

@[expose] noncomputable def f8 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 0))) (Nat.pow
    (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5
    (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 3)))
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y5.f8P (6 * g + 5)))))

@[expose] noncomputable def f10l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f10L0 (CFSG.KD.ThS.Rows_Sm_Y5.f10O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f10O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f10O0 g)

@[expose] noncomputable def f10 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp5 CFSG.KD.ThS.PT5_1 CFSG.KD.ThS.rm CFSG.KD.ThS.PR5
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5
    (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f10l0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f10P (6 * g + 5))

@[expose] noncomputable def f11l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f11L0 (CFSG.KD.ThS.Rows_Sm_Y5.f11O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f11O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f11O0 g)

@[expose] noncomputable def f11 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT5_1 (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y5.f11l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y5.f11P (8 * g + 7))

@[expose] noncomputable def f13l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f13L0 (CFSG.KD.ThS.Rows_Sm_Y5.f13O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f13O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f13O0 g)

@[expose] noncomputable def f13 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.BigS.runTree CFSG.KD.ThS.RBp5 CFSG.KD.ThS.PT5_2 CFSG.KD.ThS.rm CFSG.KD.ThS.PR5
    (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 0))
    (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 1))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5
    (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 3)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f13l0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 4)))
    (CFSG.KD.ThS.Rows_Sm_Y5.f13P (6 * g + 5))

@[expose] noncomputable def f14l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThS.Rows_Sm_Y5.f14L0 (CFSG.KD.ThS.Rows_Sm_Y5.f14O0 (g + 1) -
    CFSG.KD.ThS.Rows_Sm_Y5.f14O0 g) (CFSG.KD.ThS.Rows_Sm_Y5.f14O0 g)

@[expose] noncomputable def f14 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted CFSG.KD.ThS.PT5_2 (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 0))
    (Nat.pow (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 1)) (Nat.sub (CFSG.KC.Th.BigS.bitsN
    CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 2)) (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g +
    3))) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 4))
    (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 5))))) (CFSG.KD.ThS.Rows_Sm_Y5.f14l0 g)
    (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 6))) (CFSG.KD.ThS.Rows_Sm_Y5.f14P (8 * g + 7))

end CFSG.KD.ThS.Rows_Sm_Y5

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f2 1 as CFSG.KD.ThS.pc5_ names CFSG.KD.ThS.Rows_Sm_Y5.f2I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f2P CFSG.KD.ThS.Rows_Sm_Y5.f2l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f6 1 as CFSG.KD.ThS.bt5_0_ names CFSG.KD.ThS.Rows_Sm_Y5.f6I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f6P CFSG.KD.ThS.Rows_Sm_Y5.f6l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f7 1 as CFSG.KD.ThS.bs5_0_ names CFSG.KD.ThS.Rows_Sm_Y5.f7I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f7P CFSG.KD.ThS.Rows_Sm_Y5.f7l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f8 3 as CFSG.KD.ThS.bn5_ names CFSG.KD.ThS.Rows_Sm_Y5.f8I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f8P
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f10 1 as CFSG.KD.ThS.bt5_1_ names CFSG.KD.ThS.Rows_Sm_Y5.f10I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f10P CFSG.KD.ThS.Rows_Sm_Y5.f10l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f11 1 as CFSG.KD.ThS.bs5_1_ names CFSG.KD.ThS.Rows_Sm_Y5.f11I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f11P CFSG.KD.ThS.Rows_Sm_Y5.f11l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f13 1 as CFSG.KD.ThS.bt5_2_ names CFSG.KD.ThS.Rows_Sm_Y5.f13I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f13P CFSG.KD.ThS.Rows_Sm_Y5.f13l0
#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_Y5.f14 1 as CFSG.KD.ThS.bs5_2_ names CFSG.KD.ThS.Rows_Sm_Y5.f14I
  eval CFSG.KD.ThS.Rows_Sm_Y5.f14P CFSG.KD.ThS.Rows_Sm_Y5.f14l0

theorem CFSG.KD.ThS.sd5 : CFSG.KC.Th.andB (Nat.beq (CFSG.KD.ThS.RBp5 (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 1))) (Nat.beq (CFSG.KD.ThS.RBp5 (nat_lit 2)) (CFSG.KD.ThS.RBf (nat_lit 2))) = true :=
    by
  quickRfl

theorem CFSG.KD.ThS.pw5 : CFSG.KC.Th.BigS.pwOK CFSG.KD.ThS.RBp5 CFSG.KD.ThS.PW5 CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.PR5 (nat_lit 3) (nat_lit 5) = true := by
  quickRfl

theorem CFSG.KD.ThS.gpc5 : CFSG.KC.Th.BigS.gensPcOK CFSG.KD.ThS.GL5 (nat_lit 2) CFSG.KD.ThS.PR5
    CFSG.KD.ThS.n5 (nat_lit 32) = true := by
  quickRfl

theorem CFSG.KD.ThS.rg5 : CFSG.KC.Th.andB (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.PR5 CFSG.KD.ThS.n5
    (nat_lit 39)) (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.GL5 (nat_lit 2) (nat_lit 39)) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf5_0 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp5 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR5 (CFSG.KD.ThS.PT5_0 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (nat_lit
    5) (nat_lit 5)) (nat_lit 3) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf5_1 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp5 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR5 (CFSG.KD.ThS.PT5_1 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (nat_lit
    15) (nat_lit 5)) (nat_lit 3) = true := by
  quickRfl

theorem CFSG.KD.ThS.bf5_2 : CFSG.KC.Th.BigS.baseFixed CFSG.KD.ThS.RBp5 CFSG.KD.ThS.rm
    CFSG.KD.ThS.PR5 (CFSG.KD.ThS.PT5_2 (nat_lit 0)) (CFSG.KC.Th.BigS.bitsN CFSG.KD.ThS.BL5 (nat_lit
    25) (nat_lit 5)) (nat_lit 3) = true := by
  quickRfl

theorem CFSG.KD.ThS.bl5 : CFSG.KC.Th.BigS.blocksOK CFSG.KD.ThS.BL5 CFSG.KD.ThS.nb5 CFSG.KD.ThS.n5 =
    true := by
  quickRfl

end
