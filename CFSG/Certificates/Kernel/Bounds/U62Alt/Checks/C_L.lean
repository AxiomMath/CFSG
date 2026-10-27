module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.LceSRange
import CFSG.Certificates.Kernel.Bounds.U62Alt.Data.C_Sel
import CFSG.Certificates.Kernel.Bounds.U62Alt.Checks.C_W
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames

#kc_repo #kc_items_root CFSG.KD.U52C.LRows.P0 "CFSG/Certificates/Kernel/Bounds/U62Alt/Checks/data/C/rows/L_0_P.bin" 305 17019017700715279241
#kc_repo #kc_items_root CFSG.KD.U52C.LRows.P1 "CFSG/Certificates/Kernel/Bounds/U62Alt/Checks/data/C/rows/L_1_P.bin" 358 15083843751298121112
#kc_repo #kc_items_root CFSG.KD.U52C.LRows.P2 "CFSG/Certificates/Kernel/Bounds/U62Alt/Checks/data/C/rows/L_2_P.bin" 5810 13890523815478086469
#kc_select CFSG.KD.U52C LRows.JFs JF 841

namespace CFSG.KD.U52C.LRows

open CFSG.KD.U52C

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

end CFSG.KD.U52C.LRows

#kc_each_unfold_names CFSG.KD.U52C.LRows.sL 0 13 as CFSG.KD.U52C.sL
  eval CFSG.KD.U52C.LRows.P0 names (CFSG.KD.U52C.LRows.JFs CFSG.KD.U52C.JF)
#kc_each_unfold_names CFSG.KD.U52C.LRows.sI 0 13 as CFSG.KD.U52C.sI
  eval CFSG.KD.U52C.LRows.P1 names (CFSG.KD.U52C.LRows.JFs CFSG.KD.U52C.JF)
#kc_each_unfold CFSG.KD.U52C.LRows.sY 0 27 as CFSG.KD.U52C.sY eval CFSG.KD.U52C.LRows.P2
