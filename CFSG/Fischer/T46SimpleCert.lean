module

public import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public import Certificates.Certificate1002

public section

namespace CFSG.Fischer

open CFSG.F4.Native

theorem t46_simple_certificate : t46SimpleCertificate () = true :=
  Certificates.certificate1002

end CFSG.Fischer
