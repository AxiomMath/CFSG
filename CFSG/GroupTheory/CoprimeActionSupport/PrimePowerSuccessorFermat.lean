module


public import Mathlib.NumberTheory.Fermat
public import CFSG.LinearAlgebra.CoprimeActions.FermatDivisorBinaryOrder

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSuccessorFermat

theorem conclusion {q r d : ℕ} (hq : q.Prime) (hr : r.Prime) (hr2 : r ≠ 2) (hd : 0 < d)
    (h : r = q ^ d + 1) :
    q = 2 ∧ (∃ k : ℕ, d = 2 ^ k) ∧ ∃ j : ℕ, orderOf (2 : ZMod r) = 2 ^ j := by
  have hq2 : q = 2 := by
    by_contra hne
    have hqodd : Odd q := hq.odd_of_ne_two hne
    have : Even (q ^ d + 1) := (hqodd.pow).add_one
    rw [← h] at this
    have h2 : 2 ∣ r := even_iff_two_dvd.1 this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 h2).symm
  subst hq2
  have hr' : (2 ^ d + 1).Prime := h ▸ hr
  obtain ⟨k, hk⟩ := Nat.pow_of_pow_add_prime (by norm_num) hd.ne' hr'
  refine ⟨rfl, ⟨k, hk⟩, k + 1, ?_⟩
  have := CFSG.LinearAlgebra.CoprimeActions.FermatDivisorBinaryOrder.order_eq (k := k + 1) (q := r)
    (by omega) hr (by simp [h, hk])
  exact this

end CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSuccessorFermat
