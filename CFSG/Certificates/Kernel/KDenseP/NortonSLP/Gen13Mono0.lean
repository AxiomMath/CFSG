module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen13M "Gen13keys0.plan.txt" 23186 15248397632124883917
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen13Mono0f.items.gz" 13283725 5802668988570457761
  (cn 0 256) (on 0 256) (qn 0 256) (sel 0 256) (xsel 0 256) (wn 0 256) (psw 0 256) (sgX 0 256) (sgW 0 256) (sgA 0 256)

end
