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

#kc_repo #kc_nat_items_gz CFSG.KD.M22C "CFSG/Certificates/Kernel/Bounds/M22CovAlt/data/C.items.gz" 162481 8431811765051413956
  B[9] INV INV8 nC WT[387] RT[8] ST[1] HS LBB[34] TG[387] BIAS QQ HIGH TOP
#kc_repo #kc_items_gz CFSG.KD.M22C.JF "CFSG/Certificates/Kernel/Bounds/M22CovAlt/data/JF.bin.gz" 29036 1806507692908876078
#kc_repo #kc_items_gz CFSG.KD.M22C.CY "CFSG/Certificates/Kernel/Bounds/M22CovAlt/data/cyc.bin.gz" 880 4974623076929902037
#kc_selectT CFSG.KD.M22C blk B 9
#kc_selectT CFSG.KD.M22C selWT WT 387
#kc_select CFSG.KD.M22C selRT RT 8
#kc_select CFSG.KD.M22C selST ST 1
#kc_selectT CFSG.KD.M22C lblk LBB 34
#kc_selectT CFSG.KD.M22C TG TG 387

public section

namespace CFSG.KD.M22C

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 432)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 432)) (nat_lit 1))

@[expose] noncomputable def Cs : List Nat := CFSG.KC.LceSeg.seg JF (nat_lit 67) (nat_lit 0)

@[expose] noncomputable def cyc (j : Nat) : Bool :=
  CFSG.KC.LabZ.cycZ blk selWT LB BIAS (nat_lit 2129) (CY (Nat.mul (nat_lit 4) j))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 1))) (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 2)))
    (CY (Nat.add (Nat.mul (nat_lit 4) j) (nat_lit 3)))

end CFSG.KD.M22C

end
