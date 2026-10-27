module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import Certificates.Certificate10023
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

namespace CFSG.ComponentClassification.M12Cover

set_option compiler.extract_closed false

theorem checkK1_eq : checkK1 = true :=
  Certificates.certificate10023.1

theorem checkK3_eq : checkK3 = true :=
  Certificates.certificate10023.2.1

theorem checkQ2_eq : checkQ2 = true :=
  Certificates.certificate10023.2.2.1

theorem checkQ4_eq : checkQ4 = true :=
  Certificates.certificate10023.2.2.2.1

theorem checkQ5_eq : checkQ5 = true :=
  Certificates.certificate10023.2.2.2.2

end CFSG.ComponentClassification.M12Cover
