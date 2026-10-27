module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen13M "Gen13keys1.plan.txt" 22295 18052587341944475792
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen13Mono1f.items.gz" 12768734 8952895531557862929
  (cn 256 501) (on 256 501) (qn 256 501) (sel 256 501) (xsel 256 501) (wn 256 501) (psw 256 501) (sgX 256 501) (sgW 256 501) (sgA 256 501)

end
