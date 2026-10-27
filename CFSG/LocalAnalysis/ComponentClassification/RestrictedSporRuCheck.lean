module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
public import Certificates.Certificate2026

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

theorem ru_three_witness_check : threeWitnessOK 4060 ruCTab ruCInvTab ruQTab ruYTab 400 = true :=
  Certificates.certificate2026

end CFSG.ComponentClassification.RestrictedStd.Spor
