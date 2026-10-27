module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Base
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSixCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23Cert2Inputs
public import Certificates.Certificate4107
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.QuasithinUnique.A5.G3.M23.C2

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4107.1

theorem cert_tle : cert.tleOK RN.enc = true :=
  Certificates.certificate4107.2.1

theorem cert_latSix : latSixCheck cert [aData1, aData2] = true :=
  Certificates.certificate4107.2.2

end CFSG.QuasithinUnique.A5.G3.M23.C2
