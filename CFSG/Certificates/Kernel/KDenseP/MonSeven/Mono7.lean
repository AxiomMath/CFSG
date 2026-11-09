module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.M7M "keys7.plan.txt" 3822 4092675200801207861
#kc_repo #kc_nat_runs CFSG.KD.M7M "CFSG/Certificates/Kernel/KDenseP/MonSeven/Mono7f.items" 2197091 11045527788318255036
  (cn 638 680) (on 638 680) (qn 638 680) (sel 638 680) (xsel 638 680) (wn 638 680) (psw 638 680) (sgX 638 680) (sgW 638 680) (sgA 638 680)

end
