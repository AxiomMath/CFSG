module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.NRTM "keys4.plan.txt" 2275 4054511050995321062
#kc_repo #kc_nat_runs_gz CFSG.KD.NRTM "CFSG/Certificates/Kernel/KDenseP/Norton/Mono4f.items.gz" 1307233 2273873514384502956
  (cn 288 313) (on 288 313) (qn 288 313) (sel 288 313) (xsel 288 313) (wn 288 313) (psw 288 313) (sgX 288 313) (sgW 288 313) (sgA 288 313)

end
