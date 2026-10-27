module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
import CFSG.Certificates.Kernel.Bounds.LoadGz
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Common.LceS
public import Certificates.Data.Kernel.LceSSeg
public import Certificates.Data.Kernel.Multipliers.LabZ
public import Certificates.Data.Kernel.Multipliers.Mono

#kc_repo #kc_nat_items_gz CFSG.KD.J2C "CFSG/Certificates/Kernel/Bounds/J2CovAlt/data/C.items.gz" 64334 11568563064583320064
  B[2] INV INV8 nC WT[610] RT[5] ST[1] HS LBB[6] TG[610] BIAS QQ HIGH TOP
#kc_repo #kc_items_gz CFSG.KD.J2C.JF "CFSG/Certificates/Kernel/Bounds/J2CovAlt/data/JF.bin.gz" 4401 14456106173661300025
#kc_repo #kc_items_gz CFSG.KD.J2C.CY "CFSG/Certificates/Kernel/Bounds/J2CovAlt/data/cyc.bin.gz" 541 12868767581229182502
#kc_selectT CFSG.KD.J2C blk B 2
#kc_selectT CFSG.KD.J2C selWT WT 610
#kc_select CFSG.KD.J2C selRT RT 5
#kc_select CFSG.KD.J2C selST ST 1
#kc_selectT CFSG.KD.J2C lblk LBB 6
#kc_selectT CFSG.KD.J2C TG TG 610
#kc_repo #kc_nat_items_gz CFSG.KD.J2M "CFSG/Certificates/Kernel/Bounds/J2CovAlt/data/M.items.gz" 1601 13710444039159263120
  TBL

public section

namespace CFSG.KD.J2C

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 288)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 288)) (nat_lit 1))

@[expose] noncomputable def Cs : List Nat := CFSG.KC.LceSeg.seg JF (nat_lit 12) (nat_lit 0)

@[expose] noncomputable def cyc (j : Nat) : Bool :=
  CFSG.KC.LabZ.cycZ blk selWT LB BIAS (nat_lit 353) (CY (Nat.mul (nat_lit 4) j))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 1))) (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 2)))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 3)))

end CFSG.KD.J2C

namespace CFSG.KD.J2M

@[expose] noncomputable def Tab (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TBL (Nat.mul i (nat_lit 32))) (nat_lit 4294967295)

@[expose] noncomputable def Cst (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq k (nat_lit 2))

@[expose] def Rc : List (List Nat) :=
  [[0, 2, 0, 3, 1, 3], [0, 2, 2, 0, 3, 3, 3, 3, 3],
    [0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 0, 0,
      0, 0, 0, 0]]

@[expose] def Wc : List (List Nat) :=
  [[1, 1, 2, 0, 3, 3, 0, 2, 1], [3, 3, 0, 2, 1, 1, 2, 0, 3]]

@[expose] noncomputable def pt (x : Nat) : Bool :=
  CFSG.KC.Mono.pointOK Tab (nat_lit 2) (nat_lit 100) (nat_lit 2) Cst Rc Wc x

end CFSG.KD.J2M

end
