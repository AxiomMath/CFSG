module

public import CFSG.Certificates.Kernel.J4.M24Data.M24B_Ok
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.M24B

theorem okW_9 : ∀ t < 256, okW (2304 + t) = true := by
  kc_cover 1

end CFSG.KD.M24B

end
