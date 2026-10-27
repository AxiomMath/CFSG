module

public import Certificates.Data.Kernel.KDenseP.Mono
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.NatRunsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.GenD13M "GenD13keys2.plan.txt" 23296 14960660033126112437
#kc_repo #kc_nat_runs_gz CFSG.KD.SLP.GenD13M "CFSG/Certificates/Kernel/KDenseP/NortonSLP/GenD13Mono2f.items.gz" 13364163 3981136007324984396
  (cn 512 768) (on 512 768) (qn 512 768) (sel 512 768) (xsel 512 768) (wn 512 768) (psw 512 768) (sgX 512 768) (sgW 512 768) (sgA 512 768)

end
