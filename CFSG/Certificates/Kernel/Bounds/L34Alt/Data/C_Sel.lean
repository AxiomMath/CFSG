module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Rels
public import Certificates.Data.Kernel.Multipliers.LabZ

#kc_repo #kc_nat_items_gz CFSG.KD.L34C "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/C/lces_const.items.gz" 1606 8923228011111746670
  WT[57] RT[9] ST0 HS
#kc_selectT CFSG.KD.L34C blk B 21
#kc_selectT CFSG.KD.L34C selWT WT 57
#kc_select CFSG.KD.L34C litRT RT 9
#kc_select CFSG.KD.L34C litST ST 1
#kc_repo #kc_nat_items_gz CFSG.KD.L34C "CFSG/Certificates/Kernel/Bounds/L34Alt/Data/C/lab_const.items.gz" 321395 16275721739131392005
  LBB[83] TG[57] BIAS QQ HIGH TOP
#kc_selectT CFSG.KD.L34C lblk LBB 83
#kc_selectT CFSG.KD.L34C TG TG 57

public section

namespace CFSG.KD.L34C

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.L34Alt.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.L34Alt.sub j

@[expose] noncomputable def LB (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (lblk (Nat.shiftRight i (nat_lit 6))) (Nat.mul (Nat.land i (nat_lit 63)) (nat_lit 480)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 480)) (nat_lit 1))

end CFSG.KD.L34C

end
