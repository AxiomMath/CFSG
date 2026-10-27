module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.GenD13M "GenD13keys0.plan.txt" 23186 7975967015174334044
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.GenD13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/GenD13Mono0f.items.gz" 13353652 5549998058869215668
  (cn 0 256) (on 0 256) (qn 0 256) (sel 0 256) (xsel 0 256) (wn 0 256) (psw 0 256) (sgX 0 256) (sgW 0 256) (sgA 0 256)

end
