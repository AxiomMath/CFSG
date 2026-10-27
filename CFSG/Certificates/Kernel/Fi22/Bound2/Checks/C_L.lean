module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames
import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_Sel
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_W_0

#kc_repo #kc_items_root CFSG.KD.Fi22KC.LRows.P0 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/C/rows/L_0_P.bin" 135 4858015298024143352
#kc_repo #kc_items_root CFSG.KD.Fi22KC.LRows.P1 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/C/rows/L_1_P.bin" 1637 3046519418900283665
#kc_select CFSG.KD.Fi22KC LRows.JFs JF 351
#kc_select CFSG.KD.Fi22KC LRows.CVs CV 16

namespace CFSG.KD.Fi22KC.LRows

open CFSG.KD.Fi22KC

noncomputable def sL (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi22K.runLab selWT LB LETs HS
      (CFSG.KC.EachUnfold.nameRange JFs (P0 (4 * g + 0)) (P0 (4 * g + 1))) (P0 (4 * g + 2)))
    (P0 (4 * g + 3))

noncomputable def sY (g : Nat) : Bool :=
  CFSG.KC.Fi22K.cycOK blk selWT LB (P1 (5 * g + 0)) (P1 (5 * g + 1)) (P1 (5 * g + 2))
    (P1 (5 * g + 3)) (CVs (P1 (5 * g + 4)))

end CFSG.KD.Fi22KC.LRows

#kc_each_unfold_names CFSG.KD.Fi22KC.LRows.sL 0 6 as CFSG.KD.Fi22KC.sL
  eval CFSG.KD.Fi22KC.LRows.P0 names (CFSG.KD.Fi22KC.LRows.JFs CFSG.KD.Fi22KC.JF)
#kc_each_unfold_names CFSG.KD.Fi22KC.LRows.sY 0 16 as CFSG.KD.Fi22KC.sY
  eval CFSG.KD.Fi22KC.LRows.P1 names (CFSG.KD.Fi22KC.LRows.CVs CFSG.KD.Fi22KC.CV)
