module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Rels
public import Certificates.Data.Kernel.Multipliers.LabZ
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.U43C "CFSG/Certificates/Kernel/Bounds/U43Alt/Data/data/C/lces_const.items.gz" 11019 5132208783296739808
  WT[303] RT[9] ST0 HS
#kc_selectT CFSG.KD.U43C blk B 109
#kc_selectT CFSG.KD.U43C selWT WT 303
#kc_select CFSG.KD.U43C litRT RT 9
#kc_select CFSG.KD.U43C litST ST 1
#kc_repo #kc_nat_items_gz CFSG.KD.U43C "CFSG/Certificates/Kernel/Bounds/U43Alt/Data/data/C/lab_const.items.gz" 1695571 9654423187691470272
  LBB[436] TG[303] BIAS QQ HIGH TOP
#kc_selectT CFSG.KD.U43C lblk LBB 436
#kc_selectT CFSG.KD.U43C TG TG 303

public section

namespace CFSG.KD.U43C

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.U43Alt.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.U43Alt.sub j

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 480)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 480)) (nat_lit 1))

end CFSG.KD.U43C

end
