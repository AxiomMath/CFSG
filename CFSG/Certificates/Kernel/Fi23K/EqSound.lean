module

public import Certificates.Data.Kernel.Fi23K.Defs
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Fi23K

open CFSG.KC.Enum CFSG.KS.Raw.Orb

theorem wv_nil (G : Nat → Nat) (x : Nat) : wv G [] x = x := rfl

theorem wv_cons (G : Nat → Nat) (r : Nat) (w : List Nat) (x : Nat) :
    wv G (r :: w) x = tb G r (wv G w x) := rfl

theorem wv_append (G : Nat → Nat) (u w : List Nat) (x : Nat) :
    wv G (u ++ w) x = wv G u (wv G w x) := by
  induction u with
  | nil => rfl
  | cons r u ih => rw [List.cons_append, wv_cons, wv_cons, ih]

@[expose] def EqHolds (G : Nat → Nat) (l r : List Nat) (x : Nat) : Prop :=
  (∀ h t, l = h :: t → tb G h x < 31671) ∧ wv G l x = wv G r x

theorem eqAt_spec {G : Nat → Nat} {l r : List Nat} {x : Nat} (h : eqAt G l r x = true) :
    EqHolds G l r x := by
  unfold eqAt at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hd t e => ?_, Nat.eq_of_beq_eq_true h2⟩
  subst e
  simpa [Nat.blt_eq] using h1

theorem eqSl_spec {G : Nat → Nat} {EL ER : Nat → List Nat} {k0 nk lo c : Nat}
    (h : eqSl G EL ER k0 nk lo c = true) :
    ∀ k, k0 ≤ k → k < k0 + nk → ∀ x, lo ≤ x → x < lo + c → x < 31671 →
      EqHolds G (EL k) (ER k) x := by
  intro k hk1 hk2 x hx1 hx2 hx3
  unfold eqSl at h
  have h1 := allN_iff.1 h (x - lo) (by omega)
  rw [strictB_eq, bIf_eq] at h1
  have e : Nat.add lo (x - lo) = x := by
    change lo + (x - lo) = x
    omega
  rw [e] at h1
  simp only [Nat.blt_eq, hx3, ite_true] at h1
  have h2 := allN_iff.1 h1 (k - k0) (by omega)
  rw [strictB_eq] at h2
  have e2 : Nat.add k0 (k - k0) = k := by
    change k0 + (k - k0) = k
    omega
  rw [e2] at h2
  exact eqAt_spec h2

end CFSG.KC.Fi23K

end
