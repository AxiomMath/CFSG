module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.GenD13M "GenD13keys3.plan.txt" 11284 1575698431911242354
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.GenD13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/GenD13Mono3f.items.gz" 6489171 18235005809502314638
  (cn 768 892) (on 768 892) (qn 768 892) (sel 768 892) (xsel 768 892) (wn 768 892) (psw 768 892) (sgX 768 892) (sgW 768 892) (sgA 768 892)

end
