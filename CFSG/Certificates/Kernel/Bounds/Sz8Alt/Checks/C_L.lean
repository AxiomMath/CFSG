module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.LceSRange
import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Data.C_Sel
import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Checks.C_W
import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfoldNames

#kc_repo #kc_items_root CFSG.KD.Sz8C.LRows.P0 "CFSG/Certificates/Kernel/Bounds/Sz8Alt/Checks/data/C/rows/L_0_P.bin" 20 17885880366153656833
#kc_repo #kc_items_root CFSG.KD.Sz8C.LRows.P1 "CFSG/Certificates/Kernel/Bounds/Sz8Alt/Checks/data/C/rows/L_1_P.bin" 24 15362217737211922409
#kc_repo #kc_items_root CFSG.KD.Sz8C.LRows.P2 "CFSG/Certificates/Kernel/Bounds/Sz8Alt/Checks/data/C/rows/L_2_P.bin" 1729 14512708726513620975
#kc_select CFSG.KD.Sz8C LRows.JFs JF 44

namespace CFSG.KD.Sz8C.LRows

open CFSG.KD.Sz8C

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

end CFSG.KD.Sz8C.LRows

#kc_each_unfold_names CFSG.KD.Sz8C.LRows.sL 0 1 as CFSG.KD.Sz8C.sL
  eval CFSG.KD.Sz8C.LRows.P0 names (CFSG.KD.Sz8C.LRows.JFs CFSG.KD.Sz8C.JF)
#kc_each_unfold_names CFSG.KD.Sz8C.LRows.sI 0 1 as CFSG.KD.Sz8C.sI
  eval CFSG.KD.Sz8C.LRows.P1 names (CFSG.KD.Sz8C.LRows.JFs CFSG.KD.Sz8C.JF)
#kc_each_unfold CFSG.KD.Sz8C.LRows.sY 0 8 as CFSG.KD.Sz8C.sY eval CFSG.KD.Sz8C.LRows.P2
