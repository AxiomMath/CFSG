
module

public import CFSG.Fischer.Polar.CertBase

public import Certificates.Data.CFSGNative.Fischer.Xi22
public meta import Certificates.Data.CFSGNative.Fischer.Xi22
public import Certificates.Certificate1000

public section

namespace CFSG.Fischer

open Native

theorem polarLines_certificate : polarLinesCertificate () = true :=
  Certificates.certificate1000.1

theorem delta_certificate : deltaCertificate () = true :=
  Certificates.certificate1000.2.1

theorem hyp_certificate : hypCertificate () = true :=
  Certificates.certificate1000.2.2.1

theorem xi_certificate : xiCertificate () = true :=
  Certificates.certificate1000.2.2.2

end CFSG.Fischer
