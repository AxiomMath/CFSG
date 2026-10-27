module

public import Certificates.Data.Kernel.AS35QTS.Lens
public import CFSG.LargeExtraspecial.AS35QTSFacts
import CFSG.Certificates.Kernel.AS35QTS.ThompsonSound
public import Mathlib

public section

namespace CFSG.KC.AS35QTS

open CFSG.LargeExtraspecial.AS35QTS

theorem qtsFacts_of {G S IL W R INV CLS LN CM V0 : List Nat} (hg : gOK G = true)
    (hs : slOK G S = true) (hil : ilOK G IL = true) (hq : qpowOK G = true)
    (hr : rootOK G IL R = true) (hi : invOK G IL S INV = true) (hc : classOK G S CLS = true)
    (ho : ordOK G S = true) (hl : lineOK G S LN CM = true) (hz : nzOK G S IL W = true)
    (hw : nwOK G S W V0 LN = true) (hsw : swapOK G S IL CM = true) (hce : centOK G S = true)
    (hcz : centerOK G = true) (hlen : lensOK G S IL W V0 = true) : QtsFacts := by
  unfold lensOK at hlen
  simp only [and'_eq, Bool.and_eq_true, Nat.beq_eq, lenR_eq] at hlen
  obtain ⟨hG, hS, hIL, hW, hV⟩ := hlen
  unfold QtsFacts
  exact ⟨small_spec, lists_spec hg hG hs (by rw [lenR_eq]; exact hS), qpowOK_spec hg hG hq,
    rootOK_spec hg hG hil hr, invOK_spec hg hG hil hs hi, classOK_spec hg hG hs hc,
    ordOK_spec hg hG hs hi ho, lineOK_spec hg hG hs hi hS hl,
    nzOK_spec hg hG hil hs hi hS hW hz, nwOK_spec hg hG hil hs hi hS hV hz hl hw,
    swapOK_spec hg hG hil hs hS hIL hl hsw, centOK_spec hg hG hs hce, centerOK_spec hg hG hcz⟩

end CFSG.KC.AS35QTS

end
