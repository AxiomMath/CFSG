module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.EachUnfoldNames
import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.C_Sel
import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.C_W_0

#kc_repo #kc_items_root CFSG.KD.HSKC.LRows.P0 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/C/rows/L_0_P.bin" 42 14013506509167596805
#kc_repo #kc_items_root CFSG.KD.HSKC.LRows.P1 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/C/rows/L_1_P.bin" 104 12549115249702449190
#kc_select CFSG.KD.HSKC LRows.JFs JF 118

namespace CFSG.KD.HSKC.LRows

open CFSG.KD.HSKC

noncomputable def sL (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.HSK.runLab selWT LB LETs HS
      (CFSG.KC.EachUnfold.nameRange JFs (P0 (4 * g + 0)) (P0 (4 * g + 1))) (P0 (4 * g + 2)))
    (P0 (4 * g + 3))

noncomputable def sY (g : Nat) : Bool :=
  CFSG.KC.HSK.cycOK blk selWT LB (P1 (5 * g + 0)) (P1 (5 * g + 1)) (P1 (5 * g + 2))
    (P1 (5 * g + 3)) (P1 (5 * g + 4))

end CFSG.KD.HSKC.LRows

#kc_each_unfold_names CFSG.KD.HSKC.LRows.sL 0 2 as CFSG.KD.HSKC.sL
  eval CFSG.KD.HSKC.LRows.P0 names (CFSG.KD.HSKC.LRows.JFs CFSG.KD.HSKC.JF)
#kc_each_unfold CFSG.KD.HSKC.LRows.sY 0 1 as CFSG.KD.HSKC.sY eval CFSG.KD.HSKC.LRows.P1
