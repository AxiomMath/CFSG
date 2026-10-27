module

public import Certificates.Data.Kernel.L34Cover
public import CFSG.Certificates.Kernel.L34InvSound
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.L34Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (fget andB orB notB anyN)

variable {n w : Nat}

theorem memK_of_wit {N i x : Nat} {T : Nat → Nat} (hi : i < N) (e : T i = x) : memK N T x = true :=
  anyN_iff.2 ⟨i, hi, by rw [e]; exact Nat.beq_refl x⟩

theorem cover_sound {N L K no : Nat} {OA : Array (Array Tab)} {T ON W : Nat → Nat}
    {OT : Nat → Nat → Nat}
    (hO : OA.size = no ∧ ∀ o < no, OA[o]! = pts n w (ON o) (OT o))
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (hN : N = L * K)
    (h : ∀ s < K, covSl n w T OT ON no W L s = true) :
    coverOK n (pts n w N T) OA = true := by
  have key : ∀ k < N, T k = pidn n w ∨
      Nat.beq (pcomp n w (mask w) (T k) (T k)) (pidn n w) = false ∨
      ∃ o < no, ∃ j < ON o, OT o j = T k := by
    intro k hk
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [hN, h0, Nat.zero_mul] at hk
        exact absurd hk (Nat.not_lt_zero _)
      · exact h0
    have hs' : k / L < K := by
      rw [hN] at hk
      exact Nat.div_lt_of_lt_mul hk
    have h1 := h (k / L) hs'
    unfold covSl at h1
    rw [CFSG.KC.BfsPin.strictB_app] at h1
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (k % L) (Nat.mod_lt _ hL)
    have e : Nat.add (Nat.mul L (k / L)) (k % L) = k := Nat.div_add_mod k L
    rw [e, CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h2
    rcases CFSG.KC.L34KSnd.orB_iff.1 h2 with h3 | h3
    · exact Or.inl (Nat.eq_of_beq_eq_true h3)
    rcases CFSG.KC.L34KSnd.orB_iff.1 h3 with h4 | h4
    · exact Or.inr (Or.inl (CFSG.KC.L34KSnd.notB_iff.1 h4))
    rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h4
    obtain ⟨h5, h6⟩ := CFSG.KC.L34KSnd.andB_iff.1 h4
    obtain ⟨h7, h8⟩ := CFSG.KC.L34KSnd.andB_iff.1 h6
    exact Or.inr (Or.inr ⟨_, Nat.blt_eq.mp h5, _, Nat.blt_eq.mp h7, Nat.eq_of_beq_eq_true h8⟩)
  unfold coverOK pts
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
  rw [Array.size_ofFn] at hk
  rw [CFSG.KC.L34KSnd.pts_get hk]
  have hsz := CFSG.KC.L34KSnd.canon_sz (hc k hk)
  simp only [Bool.or_eq_true]
  rcases key k hk with h1 | h1 | ⟨o, ho, j, hj, e⟩
  · left; left
    rw [h1, ← CFSG.KC.L34KSnd.idTab_unpack' hsz]
    exact beq_self_eq_true _
  · left; right
    rw [sq_id (hc k hk), h1]
    rfl
  · right
    rw [CFSG.KC.L34KSnd.anyBelow_iff]
    have ho' : o < OA.size := by
      rw [hO.1]
      exact ho
    refine ⟨o, ho', ?_⟩
    rw [CFSG.KC.L34KSnd.map_get indexOf ho', hO.2 o ho]
    unfold pts
    exact CFSG.KC.L34KSnd.found_pts hj e

theorem conjWit_spec {N m a NA : Nat} {T CT OA H : Nat → Nat}
    (h : conjWitK n w N T m CT a NA OA H = true) :
    ∀ k < m, invNeK n w (pidn n w) a (CT k) = true → memK NA OA (CT k) = true →
      memK NA OA (pcomp n w (mask w) a (CT k)) = true →
      H k < N ∧ pcomp n w (mask w) (T (H k)) a = pcomp n w (mask w) (CT k) (T (H k)) ∧
        pcomp n w (mask w) (T (H k)) (CT k) =
          pcomp n w (mask w) (pcomp n w (mask w) a (CT k)) (T (H k)) := by
  intro k hk h1 h2 h3
  unfold conjWitK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  have h4 := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  rw [CFSG.KC.BfsPin.strictB_app] at h4
  rcases CFSG.KC.L34KSnd.orB_iff.1 h4 with h5 | h5
  · rw [CFSG.KC.L34KSnd.notB_iff, h1, h2, h3] at h5
    cases h5
  rw [CFSG.KC.BfsPin.strictB_app] at h5
  obtain ⟨h6, h7⟩ := CFSG.KC.L34KSnd.andB_iff.1 h5
  rw [CFSG.KC.BfsPin.strictB_app] at h7
  obtain ⟨h8, h9⟩ := CFSG.KC.L34KSnd.andB_iff.1 h7
  exact ⟨Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h9⟩

end CFSG.KC.L34Inv

end
