module

public import CFSG.LieType.Steinberg.Adjoint.CertE6Inputs
public import Certificates.Certificate118

public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e6AdjData_checkTables : e6AdjData.checkTables = true := by
  exact Certificates.certificate118.1

theorem e6AdjData_checkSimple : e6AdjData.checkSimple = true := by
  exact Certificates.certificate118.2.1

theorem e6AdjData_checkPairNorm : e6AdjData.checkPairNorm = true := by
  exact Certificates.certificate118.2.2

end CFSG.LieType.Steinberg.Adjoint
