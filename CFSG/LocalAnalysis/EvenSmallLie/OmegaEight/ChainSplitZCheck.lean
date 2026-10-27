module

public import Certificates.Certificate3498

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain


theorem zCheck_spec (ε : Stage1.Eps) : zCheck ε = true := by
  cases ε
  · exact Certificates.certificate3498.1
  · exact Certificates.certificate3498.2

end CFSG.EvenSmallLie.OmegaEight.Chain
