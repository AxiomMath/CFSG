module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.EachUnfoldNames
import CFSG.Certificates.Kernel.He.Bound.Data.C_Sel
import CFSG.Certificates.Kernel.He.Bound.Data.Q_Sel
import CFSG.Certificates.Kernel.He.Bound.Checks.C_W_0

#kc_repo #kc_items_root CFSG.KD.HeBC.LRows.P0 "CFSG/Certificates/Kernel/He/Bound/Checks/data/C/rows/L_0_P.bin" 20 440066650432033340
#kc_repo #kc_items_root CFSG.KD.HeBC.LRows.P1 "CFSG/Certificates/Kernel/He/Bound/Checks/data/C/rows/L_1_P.bin" 627 2882622410214754482
#kc_select CFSG.KD.HeBC LRows.JFs JF 51

namespace CFSG.KD.HeBC.LRows

open CFSG.KD.HeBC

noncomputable def sL (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.HeB.runLab selWT LB HS
      (CFSG.KC.EachUnfold.nameRange JFs (P0 (4 * g + 0)) (P0 (4 * g + 1))) (P0 (4 * g + 2)))
    (P0 (4 * g + 3))

noncomputable def sY (g : Nat) : Bool :=
  CFSG.KC.HeB.cycOK blk selWT LB (P1 (5 * g + 0)) (P1 (5 * g + 1)) (P1 (5 * g + 2))
    (P1 (5 * g + 3)) (CFSG.KC.HeB.entStk (CFSG.KD.HeBQ.selRT (P1 (5 * g + 4))))

end CFSG.KD.HeBC.LRows

#kc_each_unfold_names CFSG.KD.HeBC.LRows.sL 0 1 as CFSG.KD.HeBC.sL
  eval CFSG.KD.HeBC.LRows.P0 names (CFSG.KD.HeBC.LRows.JFs CFSG.KD.HeBC.JF)
#kc_each_unfold CFSG.KD.HeBC.LRows.sY 0 5 as CFSG.KD.HeBC.sY eval CFSG.KD.HeBC.LRows.P1
