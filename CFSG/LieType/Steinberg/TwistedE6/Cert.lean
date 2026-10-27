module

public import CFSG.LieType.Steinberg.TwistedE6.CertInputs
public import Certificates.Certificate123

public import CFSG.LieType.Steinberg.TwistedE6.Transpose
public import CFSG.LieType.Steinberg.Minuscule.Cert
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

theorem checkPerm_eq : checkPerm = true := by
  exact Certificates.certificate123.1

theorem checkRho_eq : checkRho = true := by
  exact Certificates.certificate123.2.1

theorem checkTranspose_eq : checkTranspose = true := by
  exact Certificates.certificate123.2.2.1

theorem checkSimple_eq : checkSimple = true := by
  exact Certificates.certificate123.2.2.2

end CFSG.LieType.Steinberg.TwistedE6
