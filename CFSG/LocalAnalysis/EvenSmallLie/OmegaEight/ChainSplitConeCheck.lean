module

public import Certificates.Certificate3496

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain


theorem splitConeCheck_spec (ε : Stage1.Eps) : splitConeCheck ε = true := by
  cases ε
  · exact Certificates.certificate3496.1
  · exact Certificates.certificate3496.2

end CFSG.EvenSmallLie.OmegaEight.Chain
