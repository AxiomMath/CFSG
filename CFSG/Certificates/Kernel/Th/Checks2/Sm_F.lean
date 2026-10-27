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

#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_F.f0P "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_F_0_P.bin" 194 13894596354604290697
#kc_repo #kc_items_root CFSG.KD.ThS.Rows_Sm_F.f0I "CFSG/Certificates/Kernel/Th/Checks2/data/rows/Sm_F_0_I.bin" 194 13894596354604290697

namespace CFSG.KD.ThS.Rows_Sm_F

@[expose] noncomputable def f0 (g : Nat) : Bool :=
  CFSG.KC.Th.BigS.relOK CFSG.KD.ThS.RBf CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE CFSG.KD.ThS.GRf
    CFSG.KD.ThS.IRf (CFSG.KD.ThS.Rows_Sm_F.f0P (1 * g + 0))

end CFSG.KD.ThS.Rows_Sm_F

#kc_rows_unfold CFSG.KD.ThS.Rows_Sm_F.f0 39 as CFSG.KD.ThS.rel names CFSG.KD.ThS.Rows_Sm_F.f0I eval
  CFSG.KD.ThS.Rows_Sm_F.f0P

theorem CFSG.KD.ThS.invs : CFSG.KC.Th.BigS.invOK CFSG.KD.ThS.RBf CFSG.KD.ThS.c CFSG.KD.ThS.rm
    CFSG.KD.ThS.ONE CFSG.KD.ThS.GRf CFSG.KD.ThS.IRf = true := by
  quickRfl

theorem CFSG.KD.ThS.fixW : CFSG.KC.Th.BigS.fixWOK CFSG.KD.ThS.RBf CFSG.KD.ThS.rm CFSG.KD.ThS.GRf
    CFSG.KD.ThS.w1 CFSG.KD.ThS.w2 (nat_lit 7) = true := by
  quickRfl

theorem CFSG.KD.ThS.rgf : CFSG.KC.Th.andB (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.GRf (nat_lit 8)
    (nat_lit 1004)) (CFSG.KC.Th.BigS.regsIn CFSG.KD.ThS.IRf (nat_lit 8) (nat_lit 1004)) = true := by
  quickRfl

end
