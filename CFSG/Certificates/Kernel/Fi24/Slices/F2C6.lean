module

public import CFSG.Certificates.Kernel.Fi24.Tab.F2
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.F2

theorem okC_6 : ∀ t < 296, okC (296 * 6 + t) = true := by
  kc_cover 1

end CFSG.KD.F2

end
