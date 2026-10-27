module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Rels
public import Certificates.Data.Kernel.Multipliers.LabZ
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.NatItemsGz

#kc_repo #kc_nat_items_gz CFSG.KD.U52C "CFSG/Certificates/Kernel/Bounds/U62Alt/Data/data/C/lces_const.items.gz" 9713 10349269884259547776
  WT[400] RT[20] ST0 HS
#kc_selectT CFSG.KD.U52C blk B 105
#kc_selectT CFSG.KD.U52C selWT WT 400
#kc_select CFSG.KD.U52C litRT RT 20
#kc_select CFSG.KD.U52C litST ST 1
#kc_repo #kc_nat_items_gz CFSG.KD.U52C "CFSG/Certificates/Kernel/Bounds/U62Alt/Data/data/C/lab_const.items.gz" 3426837 15265400639631485727
  LBB[419] TG[400] BIAS QQ HIGH TOP
#kc_selectT CFSG.KD.U52C lblk LBB 419
#kc_selectT CFSG.KD.U52C TG TG 400

public section

namespace CFSG.KD.U52C

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.U62Alt.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.U62Alt.sub j

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 1008)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1008)) (nat_lit 1))

end CFSG.KD.U52C

end
