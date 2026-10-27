module

public import CFSG.Certificates.Kernel.Fi24.Tab.F2
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.F2

theorem okC_1 : ∀ t < 296, okC (296 * 1 + t) = true := by
  kc_cover 1

end CFSG.KD.F2

end
