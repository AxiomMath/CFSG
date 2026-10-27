module

public import Certificates.Data.Kernel.CoverScan
public import CFSG.Certificates.Kernel.L34KSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.CoverScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

variable {n w : Nat}

theorem coverOK_of {N M : Nat} {T W ON : Nat → Nat} {OT : Nat → Nat → Nat}
    {OA : Array (Array Tab)} (hO : OA.size = M ∧ ∀ o < M, OA[o]! = pts n w (ON o) (OT o))
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true)
    (h : ∀ i < N, coverK n w M ON OT (pidn n w) (W i) (T i) = true) :
    coverOK n (pts n w N T) OA = true := by
  unfold coverOK pts
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
  rw [Array.size_ofFn] at hk
  rw [pts_get hk]
  have hsz := canon_sz (hc k hk)
  simp only [Bool.or_eq_true]
  have h1 := h k hk
  unfold coverK at h1
  rcases orB_iff.1 h1 with h2 | h2
  · left
    left
    rw [Nat.eq_of_beq_eq_true h2, ← idTab_unpack' hsz]
    exact beq_self_eq_true _
  rcases orB_iff.1 h2 with h3 | h3
  · left
    right
    cases hb : (comp n (unpack n w (T k)) (unpack n w (T k)) == idTab n)
    · rfl
    · have h4 := (invPt_iff (hc k hk)).2 (beq_iff_eq.1 hb)
      rw [notB_iff.1 h3] at h4
      cases h4
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h3
  obtain ⟨h5, h6⟩ := andB_iff.1 h3
  obtain ⟨h7, h8⟩ := andB_iff.1 h6
  right
  rw [anyBelow_iff]
  have ho : Nat.shiftRight (W k) 12 < OA.size := by
    rw [hO.1]
    exact Nat.blt_eq.mp h5
  refine ⟨_, ho, ?_⟩
  rw [map_get indexOf ho, hO.2 _ (Nat.blt_eq.mp h5)]
  unfold pts
  exact found_pts (Nat.blt_eq.mp h7) (Nat.eq_of_beq_eq_true h8)

end CFSG.KC.CoverScan

end
