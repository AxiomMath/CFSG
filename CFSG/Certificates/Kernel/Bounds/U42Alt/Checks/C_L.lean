module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.LceSRange
import CFSG.Certificates.Kernel.Bounds.U42Alt.Data.C_Sel
import CFSG.Certificates.Kernel.Bounds.U42Alt.Checks.C_W
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames

#kc_repo #kc_items_root CFSG.KD.U42C.LRows.P0 "CFSG/Certificates/Kernel/Bounds/U42Alt/Checks/data/rows/L_0_P.bin" 20 14587080457486416776
#kc_repo #kc_items_root CFSG.KD.U42C.LRows.P1 "CFSG/Certificates/Kernel/Bounds/U42Alt/Checks/data/rows/L_1_P.bin" 24 7320112042105057498
#kc_repo #kc_items_root CFSG.KD.U42C.LRows.P2 "CFSG/Certificates/Kernel/Bounds/U42Alt/Checks/data/rows/L_2_P.bin" 1280 3591622268717857149
#kc_select CFSG.KD.U42C LRows.JFs JF 15

namespace CFSG.KD.U42C.LRows

open CFSG.KD.U42C

noncomputable def sL (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.LabZ.runLabZ selWT LB TG BIAS QQ HIGH TOP
      (CFSG.KC.EachUnfold.nameRange JFs (P0 (4 * g + 0)) (P0 (4 * g + 1))) (P0 (4 * g + 2)))
    (P0 (4 * g + 3))

noncomputable def sI (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceSR.runIds selWT (P1 (5 * g + 0))
      (CFSG.KC.EachUnfold.nameRange JFs (P1 (5 * g + 1)) (P1 (5 * g + 2))) (P1 (5 * g + 3)))
    (P1 (5 * g + 4))

noncomputable def sY (g : Nat) : Bool :=
  CFSG.KC.LabZ.cycZ blk selWT LB BIAS (P2 (5 * g + 0)) (P2 (5 * g + 1)) (P2 (5 * g + 2))
    (P2 (5 * g + 3)) (P2 (5 * g + 4))

end CFSG.KD.U42C.LRows

#kc_each_unfold_names CFSG.KD.U42C.LRows.sL 0 1 as CFSG.KD.U42C.sL
  eval CFSG.KD.U42C.LRows.P0 names (CFSG.KD.U42C.LRows.JFs CFSG.KD.U42C.JF)
#kc_each_unfold_names CFSG.KD.U42C.LRows.sI 0 1 as CFSG.KD.U42C.sI
  eval CFSG.KD.U42C.LRows.P1 names (CFSG.KD.U42C.LRows.JFs CFSG.KD.U42C.JF)
#kc_each_unfold CFSG.KD.U42C.LRows.sY 0 7 as CFSG.KD.U42C.sY eval CFSG.KD.U42C.LRows.P2
