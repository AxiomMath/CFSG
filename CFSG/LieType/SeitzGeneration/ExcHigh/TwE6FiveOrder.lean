module

public import CFSG.GH74.Generic.S1.RCard

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem five_pow_dvd_prod_six (Q : ℤ) (v : ℕ) (hv : (5 : ℤ) ^ v ∣ Q + 1)
    (h5 : (5 : ℤ) ∣ Q + 1) :
    (5 : ℤ) ^ (5 * v + 1) ∣ (Q ^ 2 - (-1) ^ 2) * (Q ^ 3 - (-1) ^ 3) * (Q ^ 4 - (-1) ^ 4) *
      (Q ^ 5 - (-1) ^ 5) * (Q ^ 6 - (-1) ^ 6) := by
  have hdiv : ∀ n : ℕ, (5 : ℤ) ^ v ∣ Q ^ n - (-1) ^ n := fun n => by
    have h := sub_dvd_pow_sub_pow Q (-1) n
    rw [sub_neg_eq_add] at h
    exact dvd_trans hv h
  have hW : (5 : ℤ) ∣ Q ^ 4 - Q ^ 3 + Q ^ 2 - Q + 1 := by
    obtain ⟨m, hm⟩ := h5
    have hQ : Q = 5 * m - 1 := by linarith
    subst hQ
    exact Dvd.intro (125 * m ^ 4 - 125 * m ^ 3 + 50 * m ^ 2 - 10 * m + 1) (by ring)
  have h5' : (5 : ℤ) ^ (v + 1) ∣ Q ^ 5 - (-1) ^ 5 := by
    have e : Q ^ 5 - (-1) ^ 5 = (Q + 1) * (Q ^ 4 - Q ^ 3 + Q ^ 2 - Q + 1) := by ring
    rw [e, pow_succ (5 : ℤ) v]
    exact mul_dvd_mul hv hW
  have hprod := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (hdiv 2) (hdiv 3))
    (hdiv 4)) h5') (hdiv 6)
  have e : (5 : ℤ) ^ (5 * v + 1) =
      (5 : ℤ) ^ v * (5 : ℤ) ^ v * (5 : ℤ) ^ v * (5 : ℤ) ^ (v + 1) * (5 : ℤ) ^ v := by
    ring
  rw [e]
  exact hprod

theorem five_pow_dvd_card_statedSU_six {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1) :
    5 ^ (5 * (ℓ ^ f + 1).factorization 5 + 1) ∣ Nat.card ↥(StatedSU 6 (ℓ ^ f) K) := by
  have hc := CFSG.GH74.Generic.S1.rcard_card_statedSU h (n := 6) (by norm_num)
  have hexp : ∀ Q : ℤ, ∏ i ∈ Finset.Icc 2 6, (Q ^ i - (-1) ^ i) =
      (Q ^ 2 - (-1) ^ 2) * (Q ^ 3 - (-1) ^ 3) * (Q ^ 4 - (-1) ^ 4) * (Q ^ 5 - (-1) ^ 5) *
        (Q ^ 6 - (-1) ^ 6) := by
    intro Q
    rw [Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
      Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
      Finset.Icc_self, Finset.prod_singleton]
  have hv : (5 : ℤ) ^ (ℓ ^ f + 1).factorization 5 ∣ ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    have h' := Nat.ordProj_dvd (ℓ ^ f + 1) 5
    exact_mod_cast h'
  have h5' : (5 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    exact_mod_cast h5
  have key : (5 : ℤ) ^ (5 * (ℓ ^ f + 1).factorization 5 + 1) ∣
      (Nat.card ↥(StatedSU 6 (ℓ ^ f) K) : ℤ) := by
    rw [hc, hexp]
    exact Dvd.dvd.mul_left (five_pow_dvd_prod_six _ _ hv h5') _
  exact_mod_cast key

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
