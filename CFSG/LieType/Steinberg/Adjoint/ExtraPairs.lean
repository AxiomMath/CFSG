module

public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import CFSG.LieType.Steinberg.Adjoint.CertE8
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem f4Data_checkPairNorm : f4Data.checkPairNorm = true := by decide +kernel

theorem e8Data_checkPairNorm : e8Data.checkPairNorm = true := by decide +kernel

theorem f4Data_valid : f4Data.Valid :=
  ⟨f4Data_checkTables, f4Data_checkSimple, f4Data_checkWeyl, f4Data_checkPairs,
    f4Data_checkPairNorm⟩

theorem e8Data_valid : e8Data.Valid :=
  ⟨e8Data_checkTables, e8Data_checkSimple, e8Data_checkWeyl, e8Data_checkPairs,
    e8Data_checkPairNorm⟩

end CFSG.LieType.Steinberg.Adjoint
