module

public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import Certificates.Data.Kernel.KDense.KeysDistinct
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 200000

#kc_repo #kc_nat_items_gz CFSG.KD.KDK "CFSG/Certificates/Kernel/KDense/Data/keysort.items.gz" 532484 2197954380966582984 NK

namespace CFSG.KD.KDK

open CFSG.KC CFSG.KC.KDense

theorem keys_distinct : keysDistinctOK CFSG.KD.KDF.F NK = true := by quickRfl

end CFSG.KD.KDK

end
