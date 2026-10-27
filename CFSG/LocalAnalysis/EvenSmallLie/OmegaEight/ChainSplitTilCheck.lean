module

public import Certificates.Certificate3497

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain


theorem tilCheck_spec (ε : Stage1.Eps) : tilCheck ε = true := by
  cases ε
  · exact Certificates.certificate3497.1
  · exact Certificates.certificate3497.2

end CFSG.EvenSmallLie.OmegaEight.Chain
