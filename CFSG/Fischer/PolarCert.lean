
module

public import CFSG.Fischer.PolarCertBase

public import Certificates.Data.CFSGNative.Fischer.Polar
public meta import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Certificate1001
public import Certificates.Certificate1001Base

public section

namespace CFSG.Fischer

open Native

theorem polar_certificate : polarCertificate () = true :=
  Certificates.certificate1001

end CFSG.Fischer
