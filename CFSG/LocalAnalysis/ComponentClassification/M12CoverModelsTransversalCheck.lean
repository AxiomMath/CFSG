module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompP
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompIH
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheckInputs
public import Certificates.Certificate10025
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompP
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsDecompIH
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsCocycle
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalData

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

set_option compiler.extract_closed false

theorem rCodeCheck_eq : rCodeCheck = true :=
  Certificates.certificate10025.1

theorem cosetCheck_eq : cosetCheck = true :=
  Certificates.certificate10025.2.1

theorem decompCheck_eq : decompCheck = true :=
  Certificates.certificate10025.2.2.1

theorem betaCheck_eq : betaCheck = true :=
  Certificates.certificate10025.2.2.2.1

theorem quotCheck_eq : quotCheck = true :=
  Certificates.certificate10025.2.2.2.2.1

theorem transferCheck_eq : transferCheck = true :=
  Certificates.certificate10025.2.2.2.2.2.1

theorem lambdaCheck_eq : lambdaCheck = true :=
  Certificates.certificate10025.2.2.2.2.2.2

end CFSG.ComponentClassification.M12Cover.InternalSylow
