module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen11M "Gen11keys1.plan.txt" 23296 7412064077290093959
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.Gen11M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/Gen11Mono1f.items.gz" 13376025 8853137713827379547
  (cn 256 512) (on 256 512) (qn 256 512) (sel 256 512) (xsel 256 512) (wn 256 512) (psw 256 512) (sgX 256 512) (sgW 256 512) (sgA 256 512)

end
