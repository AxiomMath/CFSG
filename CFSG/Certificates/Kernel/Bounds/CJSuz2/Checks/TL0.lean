module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TLZ
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CFSG.KD.CJSuz2T

theorem okM_0 : ∀ t < 488, okM t = true := by
  kc_cover 1

theorem okLM_0 : ∀ t < 488, okLM t = true := fun t ht => (okLM_eq t).trans (okM_0 t ht)

end CFSG.KD.CJSuz2T

end
