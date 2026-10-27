module

public import CFSG.Certificates.Kernel.Fi24.Tab.F1
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.F1

theorem okC_0 : ∀ t < 296, okC (296 * 0 + t) = true := by
  kc_cover 1

end CFSG.KD.F1

end
