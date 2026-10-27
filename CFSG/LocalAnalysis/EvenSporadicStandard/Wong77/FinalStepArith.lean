module

public import CFSG.Monster.B.Recog.GenericGoldschmidtArith
public import CFSG.Open.OrderForm

public section

namespace CFSG.EvenSporadicStandard.Wong77

namespace FinalArith

open CFSG.Open Finset CFSG.Monster.B.Recog.GoldschmidtArith

theorem orderTwistedA_two_pow {N k : ℕ} (hN : 1 ≤ N) (hk : k ≠ 0) :
    ∃ P : ℕ, Odd P ∧ orderTwistedA N (2 ^ k) = 2 ^ (k * (N * (N + 1) / 2)) * P := by
  set Q : ℕ := ∏ i ∈ Icc 2 (N + 1), (if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1)
    with hQ
  have hQodd : Odd Q := by
    refine prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun i hi => ?_
    rw [← pow_mul]
    have hik : k * i ≠ 0 := mul_ne_zero hk (by simp at hi; omega)
    split_ifs
    · exact odd_two_pow_sub_one hik
    · exact odd_two_pow_add_one hik
  have hdvd : Nat.gcd (N + 1) (2 ^ k + 1) ∣ Q := by
    refine (Nat.gcd_dvd_right _ _).trans ((?_ : 2 ^ k + 1 ∣ (2 ^ k) ^ 2 - 1).trans ?_)
    · have h := Nat.sq_sub_sq (2 ^ k) 1
      rw [one_pow] at h
      rw [h]
      exact Dvd.intro _ rfl
    · have h2 : 2 ∈ Icc 2 (N + 1) := by simp; omega
      have := dvd_prod_of_mem (fun i => if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1) h2
      simpa using this
  obtain ⟨R, hR⟩ := hdvd
  have hg : 0 < Nat.gcd (N + 1) (2 ^ k + 1) := Nat.gcd_pos_of_pos_right _ (by positivity)
  refine ⟨R, Odd.of_dvd_nat hQodd (Dvd.intro_left _ hR.symm), ?_⟩
  rw [orderTwistedA, ← hQ, hR, ← pow_mul]
  exact Nat.div_eq_of_eq_mul_left hg (by ring)

end FinalArith

end CFSG.EvenSporadicStandard.Wong77
