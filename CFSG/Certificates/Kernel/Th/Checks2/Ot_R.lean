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

#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_R.f7P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_R_7_P.bin" 274 9960449898639397375
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_R.f7L0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_R_7_L0.bin" 3759 8062759707423164300
#kc_repo #kc_items_root CFSG.KD.ThO.Rows_Ot_R.f7O0 "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Ot_R_7_O0.bin" 9 1036397953451669203

namespace CFSG.KD.ThO.Rows_Ot_R

@[expose] noncomputable def f7l0 (g : Nat) : List Nat :=
  CFSG.KC.LceSeg.seg CFSG.KD.ThO.Rows_Ot_R.f7L0 (CFSG.KD.ThO.Rows_Ot_R.f7O0 (g + 1) -
    CFSG.KD.ThO.Rows_Ot_R.f7O0 g) (CFSG.KD.ThO.Rows_Ot_R.f7O0 g)

@[expose] noncomputable def f7 (g : Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.beq (CFSG.KC.Th.BigS.runMarked (CFSG.KD.ThO.Rows_Ot_R.f7l0 g)
    (CFSG.KD.ThO.Rows_Ot_R.f7P (4 * g + 0))) (CFSG.KD.ThO.Rows_Ot_R.f7P (4 * g + 1)))
    (CFSG.KC.Th.BigS.allMarked CFSG.KD.ThS.GRf (CFSG.KD.ThO.Rows_Ot_R.f7P (4 * g + 2))
    (CFSG.KD.ThO.Rows_Ot_R.f7P (4 * g + 3)))

end CFSG.KD.ThO.Rows_Ot_R

#kc_unfold CFSG.KD.ThO.mk CFSG.KD.ThO.Rows_Ot_R.f7 0 eval CFSG.KD.ThO.Rows_Ot_R.f7P
  CFSG.KD.ThO.Rows_Ot_R.f7l0

theorem CFSG.KD.ThO.rA : Nat.beq (CFSG.KC.Th.OutS.prodWord CFSG.KD.ThS.RBf CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThS.GRf CFSG.KD.ThS.IRf CFSG.KD.ThO.wA (nat_lit 42))
    (CFSG.KD.ThS.RBf (nat_lit 1)) = true := by
  quickRfl

theorem CFSG.KD.ThO.rB : Nat.beq (CFSG.KC.Th.OutS.prodWord CFSG.KD.ThS.RBf CFSG.KD.ThS.c
    CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThS.GRf CFSG.KD.ThS.IRf CFSG.KD.ThO.wB (nat_lit 44))
    (CFSG.KD.ThS.RBf (nat_lit 2)) = true := by
  quickRfl

theorem CFSG.KD.ThO.xb : Nat.beq (CFSG.KD.ThS.RBf (nat_lit 15)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 2)) CFSG.KD.ThS.Bi CFSG.KD.ThO.xw (nat_lit 33)) = true := by
  quickRfl

theorem CFSG.KD.ThO.xW : CFSG.KC.Th.andB (CFSG.KC.Th.chkInW CFSG.KD.ThS.rm CFSG.KD.ThS.w1
    (CFSG.KD.ThS.RBf (nat_lit 15)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2) (CFSG.KC.Th.chkInW CFSG.KD.ThS.rm
    CFSG.KD.ThS.w2 (CFSG.KD.ThS.RBf (nat_lit 15)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2) = true := by
  quickRfl

theorem CFSG.KD.ThO.yb : Nat.beq (CFSG.KD.ThS.RBf (nat_lit 11)) (CFSG.KC.Th.BigS.wordAB
    CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE (CFSG.KD.ThS.RBf (nat_lit 1)) (CFSG.KD.ThS.RBf
    (nat_lit 2)) CFSG.KD.ThS.Bi CFSG.KD.ThO.yw (nat_lit 115)) = true := by
  quickRfl

theorem CFSG.KD.ThO.yW : CFSG.KC.Th.andB (CFSG.KC.Th.chkInW CFSG.KD.ThS.rm CFSG.KD.ThS.w1
    (CFSG.KD.ThS.RBf (nat_lit 11)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2) (CFSG.KC.Th.chkInW CFSG.KD.ThS.rm
    CFSG.KD.ThS.w2 (CFSG.KD.ThS.RBf (nat_lit 11)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2) = true := by
  quickRfl

theorem CFSG.KD.ThO.bW : CFSG.KC.Th.BigS.notB (CFSG.KC.Th.andB (CFSG.KC.Th.chkInW CFSG.KD.ThS.rm
    CFSG.KD.ThS.w1 (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2) (CFSG.KC.Th.chkInW
    CFSG.KD.ThS.rm CFSG.KD.ThS.w2 (CFSG.KD.ThS.RBf (nat_lit 2)) CFSG.KD.ThS.w1 CFSG.KD.ThS.w2)) =
    true := by
  quickRfl

end
