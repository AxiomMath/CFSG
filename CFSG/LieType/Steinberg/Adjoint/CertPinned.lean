module

public import CFSG.LieType.Steinberg.Adjoint.CertPinnedInputs
public import Certificates.Certificate121

public import CFSG.LieType.Steinberg.Adjoint.CertE8
public import CFSG.Blueprint.ChevalleyPinned
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

namespace AdjData

variable {τ : Tag} (D : AdjData τ)

end AdjData

theorem f4Data_checkPinned : f4Data.checkPinned = true := by
  exact Certificates.certificate121.1

theorem e8Data_checkPinned : e8Data.checkPinned = true := by
  exact Certificates.certificate121.2

end CFSG.LieType.Steinberg.Adjoint
