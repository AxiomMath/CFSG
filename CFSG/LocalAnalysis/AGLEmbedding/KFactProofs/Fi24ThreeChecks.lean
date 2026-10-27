module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MatOpsChecks
public import Certificates.Certificate9509
public import Certificates.Certificate9510
public import Certificates.Certificate9511

public section

namespace CFSG.AGLEmbedding.R3.Fi24Three

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.Blueprint

theorem tcCheck_Fi24 :
    tcCheck (matOps 3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2 tcNregs
      tcProg tcSpec = true :=
  tcCheck_matOps 170 Certificates.certificate9509 Certificates.certificate9510

theorem cpCheck_Fi24 :
    cpCheck (matOps 3 781) NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2 cpNregs
      cpProg cpSpec = true :=
  cpCheck_matOps Certificates.certificate9511.1

theorem noFun_Fi24 : cpSpec.noFun = true :=
  Certificates.certificate9511.2

end CFSG.AGLEmbedding.R3.Fi24Three

end
