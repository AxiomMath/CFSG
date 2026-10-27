module

public import Certificates.Data.Kernel.GrpWitK
public import Certificates.Data.Kernel.L34Cover
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KC.GrpWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget andB orB notB)

variable {n w : Nat}

theorem commK_spec {lo len NC ND fw : Nat} {C D CW : Nat → Nat}
    (h : commK n w lo len NC C ND D fw CW = true) :
    ∀ a, lo ≤ a → a < lo + len → ∀ b < NC, fget (CW a) b fw < ND ∧
      D (fget (CW a) b fw) = CFSG.KS.HNA.commP n w (C a) (C b) := by
  intro a ha1 ha2 b hb
  unfold commK at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h (a - lo) (by omega)
  have e : Nat.add lo (a - lo) = a := by change lo + (a - lo) = a; omega
  rw [CFSG.KC.BfsPin.strictB_app, e, CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h1
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 b hb
  rw [CFSG.KC.BfsPin.strictB_app] at h2
  obtain ⟨h3, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 h2
  exact ⟨Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4⟩

theorem invWitK_spec {e a ND NQ : Nat} {D Q DW : Nat → Nat}
    (h : invWitK n w e a ND D NQ Q DW = true) :
    ∀ d < ND, Nat.beq (pcomp n w (mask w) (D d) (D d)) e = true →
      DW d < NQ ∧ Q (DW d) = pcomp n w (mask w) a (D d) := by
  intro d hd hsq
  unfold invWitK at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h d hd
  rw [CFSG.KC.BfsPin.strictB_app] at h1
  rcases CFSG.KC.L34KSnd.orB_iff.1 h1 with h2 | h2
  · rw [CFSG.KC.L34KSnd.notB_iff, hsq] at h2
    cases h2
  rw [CFSG.KC.BfsPin.strictB_app] at h2
  obtain ⟨h3, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 h2
  exact ⟨Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4⟩

theorem centMemK_spec {a ng NM : Nat} {G M CM : Nat → Nat}
    (h : centMemK n w a ng G NM M CM = true) :
    ∀ k < ng, pcomp n w (mask w) a (G k) = pcomp n w (mask w) (G k) a ∧ CM k < NM ∧
      M (CM k) = G k := by
  intro k hk
  unfold centMemK at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  rw [CFSG.KC.BfsPin.strictB_app] at h1
  obtain ⟨h2, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 h1
  rw [CFSG.KC.BfsPin.strictB_app] at h3
  obtain ⟨h4, h5⟩ := CFSG.KC.L34KSnd.andB_iff.1 h3
  exact ⟨Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5⟩

theorem covSl_spec {N L K no : Nat} {T ON W : Nat → Nat} {OT : Nat → Nat → Nat} (hN : N = L * K)
    (h : ∀ s < K, CFSG.KC.L34Inv.covSl n w T OT ON no W L s = true) :
    ∀ k < N, T k = pidn n w ∨
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
  unfold CFSG.KC.L34Inv.covSl at h1
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

theorem permsK_spec {N : Nat} {T : Nat → Nat} (h : permsK n w N T = true) :
    ∀ i < N, permOK n w (mask w) (n * w) (T i) (pinvS n w (mask w) (T i)) = true := by
  intro i hi
  unfold permsK at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h i hi
  rw [CFSG.KC.BfsPin.strictB_app] at h1
  exact h1

end CFSG.KC.GrpWit

end
