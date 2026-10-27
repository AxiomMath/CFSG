module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Sz8Alt.Rels
public import Certificates.Data.Kernel.Multipliers.LabZ
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Sz8C "CFSG/Certificates/Kernel/Bounds/Sz8Alt/Data/data/C/lces_const.items.gz" 1273 7799846687039519294
  WT[35] RT[8] ST0 HS
#kc_selectT CFSG.KD.Sz8C blk B 6
#kc_selectT CFSG.KD.Sz8C selWT WT 35
#kc_select CFSG.KD.Sz8C litRT RT 8
#kc_select CFSG.KD.Sz8C litST ST 1
#kc_repo #kc_nat_items_gz CFSG.KD.Sz8C "CFSG/Certificates/Kernel/Bounds/Sz8Alt/Data/data/C/lab_const.items.gz" 77247 5235675316497385414
  LBB[22] TG[35] BIAS QQ HIGH TOP
#kc_selectT CFSG.KD.Sz8C lblk LBB 22
#kc_selectT CFSG.KD.Sz8C TG TG 35

public section

namespace CFSG.KD.Sz8C

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Sz8Alt.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Sz8Alt.sub j

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 432)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 432)) (nat_lit 1))

end CFSG.KD.Sz8C

end
