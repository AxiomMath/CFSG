module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.LceSRange
import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.C_Sel
import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.C_W
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames

#kc_repo #kc_items_root CFSG.KD.L34C.LRows.P0 "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/C/rows/L_0_P.bin" 64 10842340517542179568
#kc_repo #kc_items_root CFSG.KD.L34C.LRows.P1 "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/C/rows/L_1_P.bin" 74 8785357351183785514
#kc_repo #kc_items_root CFSG.KD.L34C.LRows.P2 "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/C/rows/L_2_P.bin" 1533 12324986643679578595
#kc_select CFSG.KD.L34C LRows.JFs JF 167

namespace CFSG.KD.L34C.LRows

open CFSG.KD.L34C

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

end CFSG.KD.L34C.LRows

#kc_each_unfold_names CFSG.KD.L34C.LRows.sL 0 3 as CFSG.KD.L34C.sL
  eval CFSG.KD.L34C.LRows.P0 names (CFSG.KD.L34C.LRows.JFs CFSG.KD.L34C.JF)
#kc_each_unfold_names CFSG.KD.L34C.LRows.sI 0 3 as CFSG.KD.L34C.sI
  eval CFSG.KD.L34C.LRows.P1 names (CFSG.KD.L34C.LRows.JFs CFSG.KD.L34C.JF)
#kc_each_unfold CFSG.KD.L34C.LRows.sY 0 9 as CFSG.KD.L34C.sY eval CFSG.KD.L34C.LRows.P2
