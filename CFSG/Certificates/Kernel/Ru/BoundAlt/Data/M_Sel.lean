module

import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.M_0
public import CFSG.Certificates.Kernel.Common.LabF

#kc_repo #kc_nat_items_gz CFSG.KD.RuBAM "CFSG/Certificates/Kernel/Ru/BoundAlt/Data/data/M/lces_const.items.gz" 10659 12003081598115761659
  WT[159] RT[16] ST[10] HS nLive
#kc_selectT CFSG.KD.RuBAM blk B 14
#kc_selectT CFSG.KD.RuBAM selWT WT 159
#kc_selectT CFSG.KD.RuBAM LVs LV 1
#kc_select CFSG.KD.RuBAM litRT RT 16
#kc_select CFSG.KD.RuBAM litST ST 10
#kc_repo #kc_nat_items_gz CFSG.KD.RuBAM "CFSG/Certificates/Kernel/Ru/BoundAlt/Data/data/M/lab_const.items.gz" 143071 12182882005236469539
  L[3510]
#kc_select CFSG.KD.RuBAM LB L 3510

public section

namespace CFSG.KD.RuBAM

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.RuBAM

end
