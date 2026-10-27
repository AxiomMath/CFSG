module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

theorem l154_dvd_sq_sub_one (Q : ℕ) (hQ : 1 ≤ Q) : Q + 1 ∣ Q ^ 2 - 1 := by
  have h : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h]
  exact ⟨(Q : ℤ) - 1, by ring⟩

theorem l154_dvd_pow4_sub_one (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 2 + 1 ∣ Q ^ 4 - 1 := by
  have h : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h]
  exact ⟨(Q : ℤ) ^ 2 - 1, by ring⟩

theorem l154_dvd_pow6_sub_one (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 2 - Q + 1 ∣ Q ^ 6 - 1 := by
  have h : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ
  have h2 : Q ≤ Q ^ 2 := Nat.le_self_pow two_ne_zero Q
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h, Nat.cast_sub h2]
  exact ⟨((Q : ℤ) + 1) * ((Q : ℤ) ^ 3 - 1), by ring⟩

theorem l154_dvd_pow12_sub_one (Q : ℕ) (hQ : 1 ≤ Q) : Q ^ 4 - Q ^ 2 + 1 ∣ Q ^ 12 - 1 := by
  have h : 1 ≤ Q ^ 12 := Nat.one_le_pow _ _ hQ
  have h2 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  rw [← Int.natCast_dvd_natCast]
  push_cast [Nat.cast_sub h, Nat.cast_sub h2]
  exact ⟨((Q : ℤ) ^ 2 + 1) * ((Q : ℤ) ^ 6 - 1), by ring⟩

theorem l154_dvd_pow_sub_one_gcd {n m k r : ℕ} (h1 : r ∣ 2 ^ (n * m) - 1)
    (h2 : r ∣ 2 ^ (k * m) - 1) : r ∣ 2 ^ (Nat.gcd n k * m) - 1 := by
  have h3 : r ∣ Nat.gcd (2 ^ (n * m) - 1) (2 ^ (k * m) - 1) := Nat.dvd_gcd h1 h2
  rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_right] at h3
  exact h3

@[expose] def l154ReeOrd (q : ℕ) : ℕ :=
  q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)

theorem l154_ree_arith_core {n m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ (n * m) - 1) (hrd : r ∣ l154ReeOrd (2 ^ m)) :
    r ∣ 2 ^ (Nat.gcd n 1 * m) - 1 ∨ r ∣ 2 ^ (Nat.gcd n 2 * m) - 1 ∨ r ∣ 2 ^ (Nat.gcd n 4 * m) - 1 ∨
      r ∣ 2 ^ (Nat.gcd n 6 * m) - 1 ∨ r ∣ 2 ^ (Nat.gcd n 12 * m) - 1 := by
  have hQ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow : ∀ k : ℕ, 2 ^ (k * m) = (2 ^ m) ^ k := fun k => by
    rw [mul_comm k m, pow_mul]
  unfold l154ReeOrd at hrd
  rcases (Nat.Prime.dvd_mul hr).1 hrd with h | hF
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | hE
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | hD
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | hC
        · rcases (Nat.Prime.dvd_mul hr).1 h with hA | hB
          · have := hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow hA : r ∣ 2 ^ m)
            exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this) hr2
          · exact Or.inl (l154_dvd_pow_sub_one_gcd hrn
              (by rw [one_mul]; exact hr.dvd_of_dvd_pow hB))
        · have h' := hr.dvd_of_dvd_pow hC
          exact Or.inr (Or.inl (l154_dvd_pow_sub_one_gcd hrn
            (by rw [hpow]; exact h'.trans (l154_dvd_sq_sub_one _ hQ))))
      · have h' := hr.dvd_of_dvd_pow hD
        exact Or.inr (Or.inr (Or.inl (l154_dvd_pow_sub_one_gcd hrn
          (by rw [hpow]; exact h'.trans (l154_dvd_pow4_sub_one _ hQ)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (l154_dvd_pow_sub_one_gcd hrn
        (by rw [hpow]; exact hE.trans (l154_dvd_pow6_sub_one _ hQ))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (l154_dvd_pow_sub_one_gcd hrn
      (by rw [hpow]; exact hF.trans (l154_dvd_pow12_sub_one _ hQ))))))

theorem l154_ne_two_of_dvd_pow_sub_one {r N : ℕ} (hN : 1 ≤ N) (hr : r ∣ 2 ^ N - 1) : r ≠ 2 := by
  rintro rfl
  have h1 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  have h2 : 2 ∣ 2 ^ N - 1 + 1 := by
    rw [Nat.sub_add_cancel h1]
    exact dvd_pow_self 2 (by omega)
  omega

theorem l154_coprime_small {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 12) : Nat.gcd p k = 1 := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    (have hle := Nat.le_of_dvd (by norm_num) h
     interval_cases p <;> first | omega | exact absurd hp (by norm_num))

theorem l154_ree_arith {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    ¬ (2 ^ (p * m) - 1 ∣ l154ReeOrd (2 ^ m)) := by
  intro hdvd
  have hpm : m < p * m := by nlinarith
  have h6 : p * m ≠ 6 := by
    intro h
    have hm2 : m ≤ 1 := by nlinarith
    have : m = 1 := by omega
    subst this
    have : p = 6 := by omega
    subst this
    exact absurd hp (by norm_num)
  obtain ⟨r, hr, hrn, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (p * m) (by omega) h6
  have hr2 : r ≠ 2 := l154_ne_two_of_dvd_pow_sub_one (by omega) hrn
  have key : ∀ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 12) →
      r ∣ 2 ^ (Nat.gcd p k * m) - 1 → False := fun k hk h => by
    rw [l154_coprime_small hp hp5 hk, one_mul] at h
    exact hprim m hm hpm h
  rcases l154_ree_arith_core hr hr2 hrn (hrn.trans hdvd) with h | h | h | h | h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 4 (by simp) h
  · exact key 6 (by simp) h
  · exact key 12 (by simp) h

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
