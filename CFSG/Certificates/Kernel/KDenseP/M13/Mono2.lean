module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M13M "keys2.plan.txt" 270 3032391931308663608
#kc_repo #kc_nat_runs CFSG.KD.M13M "CFSG/Certificates/Kernel/KDenseP/M13/Mono2f.items" 156627 7127039510383622462
  (cn 76 79) (on 76 79) (qn 76 79) (sel 76 79) (xsel 76 79) (wn 76 79) (psw 76 79) (sgX 76 79) (sgW 76 79) (sgA 76 79)

end
