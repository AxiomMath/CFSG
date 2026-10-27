module

public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import Certificates.Data.Kernel.KDense.Sep
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import CFSG.Certificates.Kernel.KDense.Tactic
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 200000

#kc_repo #kc_nat_items_gz CFSG.KD.KDS "CFSG/Certificates/Kernel/KDense/Data/sep.items.gz" 4862665 15643591448436247731
    UT U MK (QS 0 15) NS
#kc_select CFSG.KD.KDS QSf QS 15

end
