module

public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.PG10P1

theorem okW_1 : ∀ t < 592, okW (592 * 1 + t) = true := by
  kc_cover 1

end CFSG.KD.PG10P1

end
