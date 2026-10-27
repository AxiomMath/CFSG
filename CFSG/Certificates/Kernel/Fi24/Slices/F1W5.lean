module

public import CFSG.Certificates.Kernel.Fi24.Tab.F1
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.F1

theorem okW_5 : ∀ t < 592, okW (592 * 5 + t) = true := by
  kc_cover 1

end CFSG.KD.F1

end
