module

public import CFSG.Certificates.Kernel.Bounds.M22CovAlt.DataM
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.M22M

open CFSG.KC

theorem sQ : Mono.paramsOK (nat_lit 2640) (nat_lit 12) Cst (nat_lit 6) = true := by
  quickRfl

theorem pt_all : ∀ x < 2640, pt x = true := by
  kc_cover 64

end CFSG.KD.M22M

end
