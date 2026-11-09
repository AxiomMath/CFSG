module

public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Checks.TLZ
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.CJSuz2T

theorem okM_1 : ∀ t < 488, okM (488 + t) = true := by
  kc_cover 1

theorem okLM_1 : ∀ t < 488, okLM (488 + t) = true :=
  fun t ht => (okLM_eq (488 + t)).trans (okM_1 t ht)

theorem okY_ok : okY = true := by quickRfl

theorem okYM_ok : okYM = true := by quickRfl

end CFSG.KD.CJSuz2T

end
