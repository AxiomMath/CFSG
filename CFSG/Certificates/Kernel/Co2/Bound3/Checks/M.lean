module

import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Co2.Bound3.Data.M
import CFSG.Certificates.Kernel.Co2.Bound3.Data.C_Sel
import CFSG.Certificates.Kernel.Co2.Bound3.Rels

#kc_repo #kc_items_root CFSG.KD.Co2KM.MRows.P0 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/M_0_P.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.Co2KM.MRows.P1 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/M_1_P.bin" 114 15409417108354689326
#kc_repo #kc_items_root CFSG.KD.Co2KM.MRows.P2 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/M_2_P.bin" 57 14941034070516702153
#kc_repo #kc_items_root CFSG.KD.Co2KM.MRows.P3 "CFSG/Certificates/Kernel/Co2/Bound3/Checks/data/rows/M_3_P.bin" 49 13872839991115951082

namespace CFSG.KD.Co2KM.MRows

open CFSG.KD.Co2KM

noncomputable def inv (g : Nat) : Bool :=
  CFSG.KC.Co2K.invol7 (FIs (P0 g))

noncomputable def hom (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Co2K.evalE FIs (XRs (P1 g))) CFSG.KC.Co2K.ONE7

noncomputable def letE (g : Nat) : Bool :=
  Nat.beq (CFSG.KD.Co2KC.LETs (P2 (3 * g + 0)))
    (CFSG.KC.Co2K.labOf (FIs (P2 (3 * g + 1))) (FIs (P2 (3 * g + 2))))

noncomputable def gw (g : Nat) : Bool :=
  Nat.beq (CFSG.KC.Co2K.gen (P3 (2 * g + 0))) (GWs (P3 (2 * g + 1)))

end CFSG.KD.Co2KM.MRows

#kc_each_unfold CFSG.KD.Co2KM.MRows.inv 0 5 as CFSG.KD.Co2KM.inv eval CFSG.KD.Co2KM.MRows.P0
#kc_each_unfold CFSG.KD.Co2KM.MRows.hom 0 23 as CFSG.KD.Co2KM.hom eval CFSG.KD.Co2KM.MRows.P1
#kc_each_unfold CFSG.KD.Co2KM.MRows.letE 0 4 as CFSG.KD.Co2KM.let eval CFSG.KD.Co2KM.MRows.P2
#kc_each_unfold CFSG.KD.Co2KM.MRows.gw 1 6 as CFSG.KD.Co2KM.gw at 0 eval CFSG.KD.Co2KM.MRows.P3
