module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys6.plan.txt" 3458 17282594776746344091
#kc_repo #kc_nat_runs_gz CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono6f.items.gz" 1985757 6208005977607394569
  (cn 600 638) (on 600 638) (qn 600 638) (sel 600 638) (xsel 600 638) (wn 600 638) (psw 600 638) (sgX 600 638) (sgW 600 638) (sgA 600 638)

end
