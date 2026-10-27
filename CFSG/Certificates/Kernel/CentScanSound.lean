module

public import Certificates.Data.Kernel.CentScan
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KC.CentScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.PSL3Four.Native
open CFSG.KLie.CT (orB notB)

variable {n w : Nat}

theorem commAll_gs {x m : Nat} {CP : Nat → Nat} {gs : Array Tab}
    (hx : canonK n w (mask w) (n * w) x = true) (hg : gs.size = m)
    (hgs : ∀ c < m, gs[c]! = unpack n w (CP c))
    (hc : ∀ c < m, canonK n w (mask w) (n * w) (CP c) = true) :
    (allBelow gs.size fun c => comp n (unpack n w x) gs[c]! == comp n gs[c]! (unpack n w x)) =
      allN m fun c => commPt n w x (CP c) := by
  rw [← commAll_eq hx hc, hg, Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff,
    CFSG.KS.BfsReplay.allBelow_iff]
  refine forall_congr' fun c => imp_congr_right fun hcm => ?_
  rw [hgs c hcm]

theorem centralOK_of {N m : Nat} {T CP : Nat → Nat} {gs : Array Tab} (hsz : szOK n w = true)
    (hT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (hg : gs.size = m)
    (hgs : ∀ c < m, gs[c]! = unpack n w (CP c))
    (hc : ∀ c < m, canonK n w (mask w) (n * w) (CP c) = true)
    (h : ∀ i < N, centIdK n w m CP (pidn n w) (T i) = true) :
    centralOK n (pts n w N T) gs = true := by
  unfold centralOK
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  rw [pts_get' hi, commAll_gs hx hg hgs hc, idTab_unpack' hsz,
    beq_unpack hx (canon_pidn hsz)]
  have h' := h i hi
  unfold centIdK at h'
  rwa [orB_eq, notB_eq] at h'

theorem offOK_of {N m s : Nat} {T CP : Nat → Nat} {gs : Array Tab}
    (hT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true)
    (hs : canonK n w (mask w) (n * w) s = true) (hg : gs.size = m)
    (hgs : ∀ c < m, gs[c]! = unpack n w (CP c))
    (hc : ∀ c < m, canonK n w (mask w) (n * w) (CP c) = true)
    (h : ∀ i < N, offK n w m CP s (T i) = true) :
    (allBelow (pts n w N T).size fun k =>
      !(allBelow gs.size fun j =>
        comp n (comp n (unpack n w s) (pts n w N T)[k]!) gs[j]! ==
          comp n gs[j]! (comp n (unpack n w s) (pts n w N T)[k]!))) = true := by
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  rw [pts_get' hi, comp_unpack' hs hx, commAll_gs (canonK_pcomp hs hx) hg hgs hc]
  have h' := h i hi
  unfold offK at h'
  rwa [notB_eq] at h'

end CFSG.KC.CentScan

end
