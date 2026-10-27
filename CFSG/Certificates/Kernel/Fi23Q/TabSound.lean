module

public import Certificates.Data.Kernel.Fi23Q.Defs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K

theorem gTab_spec {H G : Nat → Nat} {k : Nat} {w : List Nat} {lo c : Nat}
    (h : gTab H G k w lo c = true) : ∀ x, lo ≤ x → x < lo + c → tb H k x = wv G w x := by
  intro x hx1 hx2
  unfold gTab at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h (x - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h1
  have e : Nat.add lo (x - lo) = x := by
    change lo + (x - lo) = x
    omega
  rw [e] at h1
  exact Nat.eq_of_beq_eq_true h1

theorem cTab_spec {H : Nat → Nat} {k i j lo c : Nat} (h : cTab H k i j lo c = true) :
    ∀ x, lo ≤ x → x < lo + c →
      tb H k x < 31671 ∧ tb H j (tb H i (tb H k x)) = tb H i (tb H j x) := by
  intro x hx1 hx2
  unfold cTab at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h (x - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h1
  have e : Nat.add lo (x - lo) = x := by
    change lo + (x - lo) = x
    omega
  rw [e, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
  exact ⟨Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2⟩

end CFSG.KC.Fi23Q

end
