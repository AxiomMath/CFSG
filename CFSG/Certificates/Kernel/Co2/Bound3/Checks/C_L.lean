module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames
import CFSG.Certificates.Kernel.Co2.Bound3.Data.C_Sel
import CFSG.Certificates.Kernel.Co2.Bound3.Checks.C_W_0

#kc_repo #kc_items_root CFSG.KD.Co2KC.LRows.P0 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/L_0_P.bin" 20 17882113225089853293
#kc_repo #kc_items_root CFSG.KD.Co2KC.LRows.P1 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/L_1_P.bin" 148 2260364454032291974
#kc_select CFSG.KD.Co2KC LRows.JFs JF 37

namespace CFSG.KD.Co2KC.LRows

open CFSG.KD.Co2KC

noncomputable def sL (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Co2K.runLab selWT LB LETs HS
      (CFSG.KC.EachUnfold.nameRange JFs (P0 (4 * g + 0)) (P0 (4 * g + 1))) (P0 (4 * g + 2)))
    (P0 (4 * g + 3))

noncomputable def sY (g : Nat) : Bool :=
  CFSG.KC.Co2K.cycOK blk selWT LB (P1 (4 * g + 0)) (P1 (4 * g + 1)) (P1 (4 * g + 2))
    (P1 (4 * g + 3)) CFSG.KC.Co2K.NEG7

noncomputable def sZ (_ : Nat) : Bool :=
  CFSG.KC.notB (Nat.beq CFSG.KC.Co2K.NEG7 CFSG.KC.Co2K.ONE7)

end CFSG.KD.Co2KC.LRows

#kc_each_unfold_names CFSG.KD.Co2KC.LRows.sL 0 1 as CFSG.KD.Co2KC.sL
  eval CFSG.KD.Co2KC.LRows.P0 names (CFSG.KD.Co2KC.LRows.JFs CFSG.KD.Co2KC.JF)
#kc_each_unfold CFSG.KD.Co2KC.LRows.sY 0 1 as CFSG.KD.Co2KC.sY eval CFSG.KD.Co2KC.LRows.P1
#kc_unfold CFSG.KD.Co2KC.sZ CFSG.KD.Co2KC.LRows.sZ 0
