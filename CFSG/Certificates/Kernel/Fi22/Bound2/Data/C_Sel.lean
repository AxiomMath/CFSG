module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.C_0
public import CFSG.Certificates.Kernel.Fi22.Bound2.Lab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Rels

#kc_repo #kc_nat_items_gz CFSG.KD.Fi22KC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/C/lces_const.items.gz" 15708 14145622554308268497
  WT[444] RT[13] ST[13] HS
#kc_selectT CFSG.KD.Fi22KC blk B 44
#kc_selectT CFSG.KD.Fi22KC selWT WT 444
#kc_selectT CFSG.KD.Fi22KC LVs LV 2
#kc_select CFSG.KD.Fi22KC litRT RT 13
#kc_select CFSG.KD.Fi22KC litST ST 13
#kc_repo #kc_nat_items_gz CFSG.KD.Fi22KC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/C/lab_const.items.gz" 4272900 7229538231109066632
  L[11135] LET[13] CV[16]
#kc_select CFSG.KD.Fi22KC LB L 11135
#kc_select CFSG.KD.Fi22KC LETs LET 13

public section

namespace CFSG.KD.Fi22KC

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Fi22B.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Fi22K.subY j

end CFSG.KD.Fi22KC

end
