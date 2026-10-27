module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_1
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_2
public import CFSG.Certificates.Kernel.Common.LabF
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Rels

#kc_repo #kc_nat_items_gz CFSG.KD.J3AT "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/T/lces_const.items.gz" 12975 12703714508108245989
  WT[245] RT[8] ST[2] HS nLive
#kc_select CFSG.KD.J3AT blk B 154
#kc_select CFSG.KD.J3AT selWT WT 245
#kc_select CFSG.KD.J3AT LVs LV 5
#kc_select CFSG.KD.J3AT litRT RT 8
#kc_select CFSG.KD.J3AT litST ST 2
#kc_repo #kc_nat_items_gz CFSG.KD.J3AT "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/T/lab_const.items.gz" 3130005 6513660990443075030
  L[39270]
#kc_select CFSG.KD.J3AT LB L 39270

public section

namespace CFSG.KD.J3AT

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.J3A.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.J3AT

end
