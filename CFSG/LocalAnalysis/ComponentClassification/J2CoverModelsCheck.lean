module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import Certificates.Certificate10022
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.ComponentClassification.J2Cover.Models

theorem sCheck_eq : sCheck = true :=
  Certificates.certificate10022.1

theorem cosetCheck_eq : cosetCheck = true :=
  Certificates.certificate10022.2.1

theorem sDecompCheck_eq : sDecompCheck = true :=
  Certificates.certificate10022.2.2.1

theorem cocycleCheck_eq : cocycleCheck = true :=
  Certificates.certificate10022.2.2.2.1

theorem transferCheck_eq : transferCheck = true :=
  Certificates.certificate10022.2.2.2.2.1

theorem involCheck_eq : involCheck = true :=
  Certificates.certificate10022.2.2.2.2.2.1

theorem outerCheck_eq : outerCheck = true :=
  Certificates.certificate10022.2.2.2.2.2.2.1

theorem lambdaCheck_eq : lambdaCheck = true :=
  Certificates.certificate10022.2.2.2.2.2.2.2.1

theorem groupCheck_eq : groupCheck = true :=
  Certificates.certificate10022.2.2.2.2.2.2.2.2

end CFSG.ComponentClassification.J2Cover.Models
