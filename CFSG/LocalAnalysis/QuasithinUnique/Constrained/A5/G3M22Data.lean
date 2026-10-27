module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22DataInputs
public import Certificates.Certificate4106

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem m22_latSix : latSixCheck cert [m22AData] = true :=
  Certificates.certificate4106.1

theorem m22_tle : cert.tleOK RN.enc = true :=
  Certificates.certificate4106.2

end CFSG.QuasithinUnique.A5.G3
