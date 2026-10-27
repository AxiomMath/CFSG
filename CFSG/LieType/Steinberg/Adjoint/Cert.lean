module

public import CFSG.LieType.Steinberg.Adjoint.CertInputs
public import Certificates.Certificate117

public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114


public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

namespace AVec

end AVec

namespace AdjData

variable {τ : Tag} (D : AdjData τ)

end AdjData

theorem f4Data_checkTables : f4Data.checkTables = true := by
  exact Certificates.certificate117.1

theorem f4Data_checkSimple : f4Data.checkSimple = true := by
  exact Certificates.certificate117.2.1

theorem f4Data_checkWeyl : f4Data.checkWeyl = true := by
  exact Certificates.certificate117.2.2.1

theorem f4Data_checkPairs : f4Data.checkPairs = true := by
  exact Certificates.certificate117.2.2.2.1

theorem e8Data_checkTables : e8Data.checkTables = true := by
  exact Certificates.certificate117.2.2.2.2.1

theorem e8Data_checkSimple : e8Data.checkSimple = true := by
  exact Certificates.certificate117.2.2.2.2.2

theorem f4Data_check : f4Data.checkTables = true ∧ f4Data.checkSimple = true ∧
    f4Data.checkWeyl = true ∧ f4Data.checkPairs = true :=
  ⟨f4Data_checkTables, f4Data_checkSimple, f4Data_checkWeyl, f4Data_checkPairs⟩

end CFSG.LieType.Steinberg.Adjoint
