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

#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f39P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_39_P.bin" 39 13903995151933412612
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f39I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_39_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f40P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_40_P.bin" 39 4597788886903460842
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f40I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_40_I.bin" 5 18280929970295138882
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f42P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_42_P.bin" 39 9731929396451470716
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f42I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_42_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f43P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_43_P.bin" 39 4074133554820814882
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f43I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_43_I.bin" 5 18280929970295138882
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f44P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_44_P.bin" 33 2716184299901934296
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f44I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_44_I.bin" 5 15222416689836598350
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f64P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_64_P.bin" 39 5422571301598140065
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f64I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_64_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f65P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_65_P.bin" 39 4774660258267446918
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f65I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_65_I.bin" 5 18280929970295138882
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f66P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_66_P.bin" 39 13624063000183233609
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f66I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_66_I.bin" 5 15222416689836598350
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f67P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_67_P.bin" 39 2125991346247825102
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f67I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_67_I.bin" 6 14619686860213533281
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f69P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_69_P.bin" 39 3069165454620052310
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f69I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_69_I.bin" 4 14007230941556241898
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f70P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_70_P.bin" 39 10104344218754502020
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f70I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_70_I.bin" 5 18280929970295138882
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f71P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_71_P.bin" 39 15736788459956312453
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f71I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_71_I.bin" 5 15222416689836598350
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f72P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_72_P.bin" 38 17060661605138114960
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_G.f72I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_G_72_I.bin" 6 14619686860213533281

namespace CFSG.KD.ThO.Rows_Ot_G

@[expose] noncomputable def f39 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i
    CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThS.ONE (CFSG.KD.ThO.Rows_Ot_G.f39P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f39P (2 * g + 1))) CFSG.KD.ThO.Gw0A_0

@[expose] noncomputable def f40 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i
    CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThO.Gw0A_0 (CFSG.KD.ThO.Rows_Ot_G.f40P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f40P (2 * g + 1))) CFSG.KD.ThO.Gw0A_120

@[expose] noncomputable def f42 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i
    CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThS.ONE (CFSG.KD.ThO.Rows_Ot_G.f42P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f42P (2 * g + 1))) CFSG.KD.ThO.Gw0B_0

@[expose] noncomputable def f43 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i
    CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThO.Gw0B_0 (CFSG.KD.ThO.Rows_Ot_G.f43P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f43P (2 * g + 1))) CFSG.KD.ThO.Gw0B_120

@[expose] noncomputable def f44 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i
    CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThO.Gw0B_120 (CFSG.KD.ThO.Rows_Ot_G.f44P (3 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f44P (3 * g + 1))) (CFSG.KD.ThS.RBf (CFSG.KD.ThO.Rows_Ot_G.f44P (3 * g +
    2)))

@[expose] noncomputable def f64 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThS.ONE (CFSG.KD.ThO.Rows_Ot_G.f64P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f64P (2 * g + 1))) CFSG.KD.ThO.Gw1A_0

@[expose] noncomputable def f65 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1A_0 (CFSG.KD.ThO.Rows_Ot_G.f65P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f65P (2 * g + 1))) CFSG.KD.ThO.Gw1A_120

@[expose] noncomputable def f66 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1A_120 (CFSG.KD.ThO.Rows_Ot_G.f66P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f66P (2 * g + 1))) CFSG.KD.ThO.Gw1A_240

@[expose] noncomputable def f67 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1A_240 (CFSG.KD.ThO.Rows_Ot_G.f67P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f67P (2 * g + 1))) CFSG.KD.ThO.Gw1A_360

@[expose] noncomputable def f69 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThS.ONE (CFSG.KD.ThO.Rows_Ot_G.f69P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f69P (2 * g + 1))) CFSG.KD.ThO.Gw1B_0

@[expose] noncomputable def f70 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1B_0 (CFSG.KD.ThO.Rows_Ot_G.f70P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f70P (2 * g + 1))) CFSG.KD.ThO.Gw1B_120

@[expose] noncomputable def f71 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1B_120 (CFSG.KD.ThO.Rows_Ot_G.f71P (2 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f71P (2 * g + 1))) CFSG.KD.ThO.Gw1B_240

@[expose] noncomputable def f72 (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i
    CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1B_240 (CFSG.KD.ThO.Rows_Ot_G.f72P (3 * g + 0))
    (CFSG.KD.ThO.Rows_Ot_G.f72P (3 * g + 1))) (CFSG.KD.ThS.RBf (CFSG.KD.ThO.Rows_Ot_G.f72P (3 * g +
    2)))

end CFSG.KD.ThO.Rows_Ot_G

#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f39 1 as CFSG.KD.ThO.gw0A_ names CFSG.KD.ThO.Rows_Ot_G.f39I
  eval CFSG.KD.ThO.Rows_Ot_G.f39P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f40 1 as CFSG.KD.ThO.gw0A_ names CFSG.KD.ThO.Rows_Ot_G.f40I
  eval CFSG.KD.ThO.Rows_Ot_G.f40P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f42 1 as CFSG.KD.ThO.gw0B_ names CFSG.KD.ThO.Rows_Ot_G.f42I
  eval CFSG.KD.ThO.Rows_Ot_G.f42P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f43 1 as CFSG.KD.ThO.gw0B_ names CFSG.KD.ThO.Rows_Ot_G.f43I
  eval CFSG.KD.ThO.Rows_Ot_G.f43P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f44 1 as CFSG.KD.ThO.gw0B_ names CFSG.KD.ThO.Rows_Ot_G.f44I
  eval CFSG.KD.ThO.Rows_Ot_G.f44P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f64 1 as CFSG.KD.ThO.gw1A_ names CFSG.KD.ThO.Rows_Ot_G.f64I
  eval CFSG.KD.ThO.Rows_Ot_G.f64P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f65 1 as CFSG.KD.ThO.gw1A_ names CFSG.KD.ThO.Rows_Ot_G.f65I
  eval CFSG.KD.ThO.Rows_Ot_G.f65P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f66 1 as CFSG.KD.ThO.gw1A_ names CFSG.KD.ThO.Rows_Ot_G.f66I
  eval CFSG.KD.ThO.Rows_Ot_G.f66P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f67 1 as CFSG.KD.ThO.gw1A_ names CFSG.KD.ThO.Rows_Ot_G.f67I
  eval CFSG.KD.ThO.Rows_Ot_G.f67P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f69 1 as CFSG.KD.ThO.gw1B_ names CFSG.KD.ThO.Rows_Ot_G.f69I
  eval CFSG.KD.ThO.Rows_Ot_G.f69P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f70 1 as CFSG.KD.ThO.gw1B_ names CFSG.KD.ThO.Rows_Ot_G.f70I
  eval CFSG.KD.ThO.Rows_Ot_G.f70P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f71 1 as CFSG.KD.ThO.gw1B_ names CFSG.KD.ThO.Rows_Ot_G.f71I
  eval CFSG.KD.ThO.Rows_Ot_G.f71P
#kc_rows_unfold CFSG.KD.ThO.Rows_Ot_G.f72 1 as CFSG.KD.ThO.gw1B_ names CFSG.KD.ThO.Rows_Ot_G.f72I
  eval CFSG.KD.ThO.Rows_Ot_G.f72P

theorem CFSG.KD.ThO.gt3 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThS.RBf
    (nat_lit 1)) (CFSG.KD.ThS.RBf (nat_lit 2))) CFSG.KD.ThO.Gt3 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt4 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt3
    (CFSG.KD.ThS.RBf (nat_lit 2))) CFSG.KD.ThO.Gt4 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt5 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt3
    CFSG.KD.ThO.Gt4) CFSG.KD.ThO.Gt5 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt6 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt3
    CFSG.KD.ThO.Gt5) CFSG.KD.ThO.Gt6 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt7 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThS.RBf
    (nat_lit 1)) CFSG.KD.ThO.Gt6) CFSG.KD.ThO.Gt7 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt8 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt6
    (CFSG.KD.ThS.RBf (nat_lit 1))) CFSG.KD.ThO.Gt8 = true := by
  quickRfl

theorem CFSG.KD.ThO.gt8i : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt8
    CFSG.KD.ThO.Gt8i) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gu : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt8i
    CFSG.KD.ThO.Gt7) CFSG.KD.ThO.Gu = true := by
  quickRfl

theorem CFSG.KD.ThO.gs8 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt6
    CFSG.KD.ThO.Gt5) CFSG.KD.ThO.Gs8 = true := by
  quickRfl

theorem CFSG.KD.ThO.gs9 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt3
    CFSG.KD.ThO.Gs8) CFSG.KD.ThO.Gs9 = true := by
  quickRfl

theorem CFSG.KD.ThO.gs10 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gs9
    CFSG.KD.ThO.Gt4) CFSG.KD.ThO.Gs10 = true := by
  quickRfl

theorem CFSG.KD.ThO.gs7 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (CFSG.KD.ThS.RBf
    (nat_lit 1)) CFSG.KD.ThO.Gs10) CFSG.KD.ThO.Gs7 = true := by
  quickRfl

theorem CFSG.KD.ThO.gs8p : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gs10
    (CFSG.KD.ThS.RBf (nat_lit 1))) CFSG.KD.ThO.Gs8p = true := by
  quickRfl

theorem CFSG.KD.ThO.gs8pi : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gs8p
    CFSG.KD.ThO.Gs8pi) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gv : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gs8pi
    CFSG.KD.ThO.Gs7) CFSG.KD.ThO.Gv = true := by
  quickRfl

theorem CFSG.KD.ThO.gx : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    CFSG.KD.ThO.Gv (nat_lit 14) (nat_lit 4)) CFSG.KD.ThO.Gx = true := by
  quickRfl

theorem CFSG.KD.ThO.gu9 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    CFSG.KD.ThO.Gu (nat_lit 9) (nat_lit 4)) CFSG.KD.ThO.Gu9 = true := by
  quickRfl

theorem CFSG.KD.ThO.gy : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gt7
    CFSG.KD.ThO.Gu9) CFSG.KD.ThO.Gy = true := by
  quickRfl

theorem CFSG.KD.ThO.gxy : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gx
    CFSG.KD.ThO.Gy) CFSG.KD.ThO.Gxy = true := by
  quickRfl

theorem CFSG.KD.ThO.gq0 : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE
    CFSG.KD.ThO.Gxy (nat_lit 6) (nat_lit 3)) CFSG.KD.ThO.Gq0 = true := by
  quickRfl

theorem CFSG.KD.ThO.gg0 : Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit 1)) (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.Bi
    (nat_lit 276) (nat_lit 5)) CFSG.KD.ThO.Gg0 = true := by
  quickRfl

theorem CFSG.KD.ThO.ggi0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gg0
    CFSG.KD.ThO.Ggi0) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gm0a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ggi0
    CFSG.KD.ThO.Gq0) CFSG.KD.ThO.Gm0a = true := by
  quickRfl

theorem CFSG.KD.ThO.gm0b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm0a
    CFSG.KD.ThO.Gg0) CFSG.KD.ThO.Gm0b = true := by
  quickRfl

theorem CFSG.KD.ThO.gm0c : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm0b
    (CFSG.KD.ThS.RBf (nat_lit 1))) CFSG.KD.ThO.Gm0c = true := by
  quickRfl

theorem CFSG.KD.ThO.gm0d : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThO.Gm0c (nat_lit 9) (nat_lit 4)) CFSG.KD.ThO.Gm0d = true := by
  quickRfl

theorem CFSG.KD.ThO.gc0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm0d
    CFSG.KD.ThO.Ggi0) CFSG.KD.ThO.Gc0 = true := by
  quickRfl

theorem CFSG.KD.ThO.gci0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gc0
    CFSG.KD.ThO.Gci0) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gf0a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gc0
    CFSG.KD.ThO.Gq0) CFSG.KD.ThO.Gf0a = true := by
  quickRfl

theorem CFSG.KD.ThO.gf0 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gf0a
    CFSG.KD.ThO.Gci0) CFSG.KD.ThO.Gf0 = true := by
  quickRfl

theorem CFSG.KD.ThO.gfa0 : Nat.beq CFSG.KD.ThO.Gf0 (CFSG.KD.ThS.RBf (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThO.gh01a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gx
    CFSG.KD.ThO.Gc0) CFSG.KD.ThO.Gh01a = true := by
  quickRfl

theorem CFSG.KD.ThO.gh01b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gci0
    CFSG.KD.ThO.Gh01a) CFSG.KD.ThO.Gh01b = true := by
  quickRfl

theorem CFSG.KD.ThO.ge01 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gx
    CFSG.KD.ThO.Gh01b) CFSG.KD.ThO.Ge01 = true := by
  quickRfl

theorem CFSG.KD.ThO.ge01i : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge01
    CFSG.KD.ThO.Ge01i) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gh02a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gy
    CFSG.KD.ThO.Gc0) CFSG.KD.ThO.Gh02a = true := by
  quickRfl

theorem CFSG.KD.ThO.gh02b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gci0
    CFSG.KD.ThO.Gh02a) CFSG.KD.ThO.Gh02b = true := by
  quickRfl

theorem CFSG.KD.ThO.ge02 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gy
    CFSG.KD.ThO.Gh02b) CFSG.KD.ThO.Ge02 = true := by
  quickRfl

theorem CFSG.KD.ThO.ge02i : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge02
    CFSG.KD.ThO.Ge02i) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gw0A_240 : Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThO.Ge01 CFSG.KD.ThO.Ge01i CFSG.KD.ThO.Ge02 CFSG.KD.ThO.Ge02i CFSG.KD.ThO.Gw0A_120
    (nat_lit 6761439539694400935) (nat_lit 32)) (CFSG.KD.ThS.RBf (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThO.gg1 : Nat.beq (CFSG.KC.Th.BigS.wordAB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit 1)) (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.Bi
    (nat_lit 17896517) (nat_lit 13)) CFSG.KD.ThO.Gg1 = true := by
  quickRfl

theorem CFSG.KD.ThO.ggi1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gg1
    CFSG.KD.ThO.Ggi1) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gm1a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ggi1
    CFSG.KD.ThO.Gx) CFSG.KD.ThO.Gm1a = true := by
  quickRfl

theorem CFSG.KD.ThO.gm1b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm1a
    CFSG.KD.ThO.Gg1) CFSG.KD.ThO.Gm1b = true := by
  quickRfl

theorem CFSG.KD.ThO.gm1c : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm1b
    (CFSG.KD.ThS.RBf (nat_lit 1))) CFSG.KD.ThO.Gm1c = true := by
  quickRfl

theorem CFSG.KD.ThO.gm1d : Nat.beq (CFSG.KC.Th.BigS.powB CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThO.Gm1c (nat_lit 9) (nat_lit 4)) CFSG.KD.ThO.Gm1d = true := by
  quickRfl

theorem CFSG.KD.ThO.gc1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gm1d
    CFSG.KD.ThO.Ggi1) CFSG.KD.ThO.Gc1 = true := by
  quickRfl

theorem CFSG.KD.ThO.gci1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gc1
    CFSG.KD.ThO.Gci1) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gf1a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gc1
    CFSG.KD.ThO.Gx) CFSG.KD.ThO.Gf1a = true := by
  quickRfl

theorem CFSG.KD.ThO.gf1 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gf1a
    CFSG.KD.ThO.Gci1) CFSG.KD.ThO.Gf1 = true := by
  quickRfl

theorem CFSG.KD.ThO.gfa1 : Nat.beq CFSG.KD.ThO.Gf1 (CFSG.KD.ThS.RBf (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThO.gh11a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gx
    CFSG.KD.ThO.Gc1) CFSG.KD.ThO.Gh11a = true := by
  quickRfl

theorem CFSG.KD.ThO.gh11b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gci1
    CFSG.KD.ThO.Gh11a) CFSG.KD.ThO.Gh11b = true := by
  quickRfl

theorem CFSG.KD.ThO.ge11 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gx
    CFSG.KD.ThO.Gh11b) CFSG.KD.ThO.Ge11 = true := by
  quickRfl

theorem CFSG.KD.ThO.ge11i : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge11
    CFSG.KD.ThO.Ge11i) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gh12a : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gy
    CFSG.KD.ThO.Gc1) CFSG.KD.ThO.Gh12a = true := by
  quickRfl

theorem CFSG.KD.ThO.gh12b : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gci1
    CFSG.KD.ThO.Gh12a) CFSG.KD.ThO.Gh12b = true := by
  quickRfl

theorem CFSG.KD.ThO.ge12 : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Gy
    CFSG.KD.ThO.Gh12b) CFSG.KD.ThO.Ge12 = true := by
  quickRfl

theorem CFSG.KD.ThO.ge12i : Nat.beq (CFSG.KC.Th.mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThO.Ge12
    CFSG.KD.ThO.Ge12i) CFSG.KD.ThS.ONE = true := by
  quickRfl

theorem CFSG.KD.ThO.gw1A_480 : Nat.beq (CFSG.KC.Th.OutS.prod4 CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThO.Ge11 CFSG.KD.ThO.Ge11i CFSG.KD.ThO.Ge12 CFSG.KD.ThO.Ge12i CFSG.KD.ThO.Gw1A_360
    (nat_lit 4545000243104208823911) (nat_lit 36)) (CFSG.KD.ThS.RBf (nat_lit 1)) = true := by
  quickRfl

end
