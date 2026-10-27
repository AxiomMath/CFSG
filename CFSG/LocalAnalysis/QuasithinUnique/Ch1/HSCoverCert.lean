module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck
public import Certificates.Certificate4085

public section

namespace CFSG.QuasithinUnique.Ch1.HSCover

theorem covCheck_covData : covCheck covData = true :=
  Certificates.certificate4085.1

theorem covData_nV : covData.nV = 512 :=
  Certificates.certificate4085.2

end CFSG.QuasithinUnique.Ch1.HSCover
