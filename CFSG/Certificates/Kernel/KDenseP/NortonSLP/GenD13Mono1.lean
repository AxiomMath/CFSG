module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.GenD13M "GenD13keys1.plan.txt" 23296 5726904813406980870
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.GenD13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/GenD13Mono1f.items.gz" 13379806 13400339969233738819
  (cn 256 512) (on 256 512) (qn 256 512) (sel 256 512) (xsel 256 512) (wn 256 512) (psw 256 512) (sgX 256 512) (sgW 256 512) (sgA 256 512)

end
