module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QAsm
public import Certificates.Certificate6133

public section

namespace CFSG.OddStandard.Solomon75

theorem lemma57_of_certificate (hF : Solomon75Frac53) :
    Solomon75Lemma57 :=
  lemma57 hF Certificates.certificate6133

end CFSG.OddStandard.Solomon75
