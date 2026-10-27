module

public import Certificates.Data.Kernel.G24Tri
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KC.G24Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSporadicStandard.G24Aut
  CFSG.Monster.B.Co2.Native

variable {t : Nat} (hid : unpack 1365 11 (pidn 1365 11) = idA 1365)
  (ht : canonK 1365 11 (mask 11) (1365 * 11) t = true)
include hid ht

theorem ordAux_of : ∀ d p, ordAuxK t d p = true →
    ordAux (unpack 1365 11 t) d (unpack 1365 11 p) = true
  | 0, p, h => by
    have e : p = pidn 1365 11 := Nat.eq_of_beq_eq_true h
    subst e
    rw [ordAux, ← hid]
    exact eqK_sound (Nat.beq_refl _)
  | d + 1, p, h => by
    have h' : (neIdK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) p &&
        ordAuxK t d (pcomp 1365 11 (mask 11) t p)) = true := h
    rw [Bool.and_eq_true] at h'
    have hp : canonK 1365 11 (mask 11) (1365 * 11) p = true := by
      have h1 := h'.1
      unfold neIdK at h1
      cases hc : canonK 1365 11 (mask 11) (1365 * 11) p
      · rw [hc] at h1
        exact absurd h1 Bool.false_ne_true
      · rfl
    rw [ordAux, neIdK_sound h'.1, CFSG.KC.BfsPin.compA_unpack ht hp]
    exact ordAux_of d _ h'.2

theorem ordIs_of {v : Nat} (hv : 0 < v) (h : ordAuxK t (v - 1) t = true) :
    CFSG.EvenSporadicStandard.G24Aut.ordIs (unpack 1365 11 t) v = true := by
  unfold CFSG.EvenSporadicStandard.G24Aut.ordIs
  rw [ordAux_of hid ht _ _ h, decide_eq_true hv]
  rfl

end CFSG.KC.G24Tri

end
