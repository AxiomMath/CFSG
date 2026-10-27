module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem orderOf_eq_two_of_invA {n : ℕ} {t : Array ℕ} {τ : Equiv.Perm (Fin n)}
    (ht : CFSG.Monster.B.Co2.Rep n t τ) (h : invA n t = true) : orderOf τ = 2 := by
  simp only [invA, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h1 : τ ≠ 1 := fun e => by
    have := (eqA_iff ht rep_idA).2 e
    rw [h.1] at this
    exact Bool.false_ne_true this
  have h2 : τ * τ = 1 := (eqA_iff (rep_compA ht ht) rep_idA).1 h.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rwa [pow_two]) h1

end CFSG.EvenSporadicStandard.RuStd.S2
