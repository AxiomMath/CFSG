module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.M22CoverCheck
public import Certificates.Certificate4101
public meta import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.QuasithinUnique.Ch1.M22Cover

theorem covCheck_covData : covCheck covData = true :=
  Certificates.certificate4101.1

theorem covData_nV : covData.nV = 128 :=
  Certificates.certificate4101.2.1

theorem covData_free : covData.free = [189] :=
  Certificates.certificate4101.2.2

end CFSG.QuasithinUnique.Ch1.M22Cover
