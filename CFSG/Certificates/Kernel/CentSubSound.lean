module

public import Certificates.Data.Kernel.CentSub
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.CentSub

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.PSL3Four.Native
open CFSG.KLie.CT (orB notB)

variable {n w : Nat}

theorem centSubK_sound {CN ZN x : Nat} {CP ZP : Nat → Nat}
    (hx : canonK n w (mask w) (n * w) x = true)
    (hc : ∀ c < CN, canonK n w (mask w) (n * w) (CP c) = true)
    (h : centSubK n w CN CP ZN ZP x = true)
    (hcomm : ∀ c < CN,
      comp n (unpack n w x) (unpack n w (CP c)) = comp n (unpack n w (CP c)) (unpack n w x)) :
    ∃ k < ZN, x = ZP k := by
  have hall : (allN CN fun c => commPt n w x (CP c)) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun c hc' => (commPt_iff hx (hc c hc')).2 (hcomm c hc')
  unfold centSubK at h
  rw [orB_eq, notB_eq, notB_eq, hall] at h
  by_contra hne
  have hz : (allN ZN fun k => CFSG.KLie.CT.notB (Nat.beq x (ZP k))) = true := by
    refine CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => ?_
    rw [notB_eq]
    cases hb : Nat.beq x (ZP k)
    · rfl
    · exact absurd ⟨k, hk, Nat.eq_of_beq_eq_true hb⟩ hne
  rw [hz] at h
  exact absurd h (by decide)

end CFSG.KC.CentSub

end
