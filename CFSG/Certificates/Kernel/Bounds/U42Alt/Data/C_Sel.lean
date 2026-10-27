module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.U42Alt.Rels
public import Certificates.Data.Kernel.Multipliers.LabZ
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.U42C "CFSG/Certificates/Kernel/Bounds/U42Alt/Data/data/lces_const.items.gz" 673 11073444841306787749
  WT[21] RT[7] ST0 HS
#kc_selectT CFSG.KD.U42C blk B 2
#kc_selectT CFSG.KD.U42C selWT WT 21
#kc_select CFSG.KD.U42C litRT RT 7
#kc_select CFSG.KD.U42C litST ST 1
#kc_repo #kc_nat_items_gz CFSG.KD.U42C "CFSG/Certificates/Kernel/Bounds/U42Alt/Data/data/lab_const.items.gz" 23411 10361371899978907298
  LBB[8] TG[21] BIAS QQ HIGH TOP
#kc_selectT CFSG.KD.U42C lblk LBB 8
#kc_selectT CFSG.KD.U42C TG TG 21

public section

namespace CFSG.KD.U42C

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.U42Alt.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.U42Alt.sub j

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 384)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 384)) (nat_lit 1))

end CFSG.KD.U42C

end
