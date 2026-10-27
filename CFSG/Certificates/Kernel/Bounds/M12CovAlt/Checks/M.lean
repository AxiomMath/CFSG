module

public import CFSG.Certificates.Kernel.Bounds.M12CovAlt.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.M12M

open CFSG.KC

theorem sQ : Mono.paramsOK (nat_lit 12) (nat_lit 2) Cst (nat_lit 3) = true := by
  quickRfl

theorem pt_all : ∀ x < 12, pt x = true := by
  kc_cover 4

end CFSG.KD.M12M

end
