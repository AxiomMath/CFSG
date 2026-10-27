module

public import CFSG.Certificates.Kernel.Bounds.J2CovAlt.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.J2M

open CFSG.KC

theorem sQ : Mono.paramsOK (nat_lit 100) (nat_lit 2) Cst (nat_lit 3) = true := by
  quickRfl

theorem pt_all : ∀ x < 100, pt x = true := by
  kc_cover 10

end CFSG.KD.J2M

end
