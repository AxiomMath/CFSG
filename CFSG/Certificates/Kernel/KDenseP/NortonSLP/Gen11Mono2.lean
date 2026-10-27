module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen11M "Gen11keys2.plan.txt" 21476 4680501024599479944
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen11M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen11Mono2f.items.gz" 12320185 9681822614185286508
  (cn 512 748) (on 512 748) (qn 512 748) (sel 512 748) (xsel 512 748) (wn 512 748) (psw 512 748) (sgX 512 748) (sgW 512 748) (sgA 512 748)

end
