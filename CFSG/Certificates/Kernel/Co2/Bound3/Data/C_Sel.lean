module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.C_0
public import CFSG.Certificates.Kernel.Co2.Bound3.Lab
public import CFSG.Certificates.Kernel.Co2.Bound3.Rels
public import CFSG.Certificates.Kernel.Co2.Bound.Rels

#kc_repo #kc_nat_items_gz CFSG.KD.Co2KC "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_C_lces_const.items.gz" 43447 6127142160858842498
  WT[1144] RT[10] ST[4] HS
#kc_selectT CFSG.KD.Co2KC blk B 5
#kc_selectT CFSG.KD.Co2KC selWT WT 1144
#kc_selectT CFSG.KD.Co2KC LVs LV 1
#kc_select CFSG.KD.Co2KC litRT RT 10
#kc_select CFSG.KD.Co2KC litST ST 4
#kc_repo #kc_nat_items_gz CFSG.KD.Co2KC "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_C_lab_const.items.gz" 355688 16052155844200973476
  L[1170] LET[4]
#kc_select CFSG.KD.Co2KC LB L 1170
#kc_select CFSG.KD.Co2KC LETs LET 4

public section

namespace CFSG.KD.Co2KC

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Co2B.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Co2K.subH j

end CFSG.KD.Co2KC

end
