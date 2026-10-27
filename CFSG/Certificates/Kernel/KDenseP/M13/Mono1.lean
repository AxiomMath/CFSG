module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M13M "keys1.plan.txt" 3420 13323279173671950666
#kc_repo #kc_nat_runs_gz CFSG.KD.M13M "CFSG/Certificates/Kernel/KDenseP/M13/Mono1f.items.gz" 1938103 5106530452925793296
  (cn 38 76) (on 38 76) (qn 38 76) (sel 38 76) (xsel 38 76) (wn 38 76) (psw 38 76) (sgX 38 76) (sgW 38 76) (sgA 38 76)

end
