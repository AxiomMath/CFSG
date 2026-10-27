module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.HE7M "keys0.plan.txt" 3050 8515270875324788800

#kc_repo #kc_nat_runs_gz CFSG.KD.HE7M "CFSG/Certificates/Kernel/KDenseP/HeSeven/Mono0f.items.gz" 1772928 9314644192484993012
  (cn 0 34) (on 0 34) (qn 0 34) (sel 0 34) (xsel 0 34) (wn 0 34) (psw 0 34) (sgX 0 34) (sgW 0 34) (sgA 0 34)

end
