module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.NRTM "keys1.plan.txt" 6524 10083990000948104668
#kc_repo #kc_nat_runs_gz CFSG.KD.NRTM "CFSG/Certificates/Kernel/KDenseP/Norton/Mono1f.items.gz" 3755610 8511691335264509936
  (cn 72 144) (on 72 144) (qn 72 144) (sel 72 144) (xsel 72 144) (wn 72 144) (psw 72 144) (sgX 72 144) (sgW 72 144) (sgA 72 144)

end
