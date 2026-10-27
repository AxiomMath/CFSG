module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} {K : Type} [Field K]

theorem card_hypSU_three (h : UnitaryFieldData p 1 K) :
    Nat.card (hypSU h 1 1) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have hp1 : 1 ≤ p := h.prime.one_lt.le
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨-, -, -, -, -, hS, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hI : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)] at hS
  have hZ : (Nat.card (hypSU h 1 1) : ℤ) =
      ((p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) : ℕ) : ℤ) := by
    rw [hS]
    push_cast [h1]
    norm_num
  exact_mod_cast hZ

theorem not_card_dvd_of_sylow_hyp (h : UnitaryFieldData p 1 K) (hp2 : p ≠ 2)
    (Q : Sylow 2 (hypPSU h 1 1)) : ¬ Nat.card Q ∣ p * (p ^ 2 - 1) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := h.prime
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hPZ := card_hypPSU_mul h (r := 1) (ε := 1)
  have hZ := card_hypScalars h (r := 1) (ε := 1) (by norm_num)
  rw [card_hypSU_three h] at hPZ
  have hzodd : ¬ 2 ∣ Nat.card (hypScalars h 1 1) := by
    have hdz : Nat.card (hypScalars h 1 1) ∣ 3 := by
      rw [hZ]
      exact Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 hdz with h1 | h1 <;> rw [h1] <;> omega
  have hN0 : Nat.card (hypPSU h 1 1) ≠ 0 := Nat.card_pos.ne'
  have hz0 : Nat.card (hypScalars h 1 1) ≠ 0 := Nat.card_pos.ne'
  have hQ : Nat.card Q = 2 ^ padicValNat 2 (Nat.card (hypPSU h 1 1)) := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ Nat.prime_two]
  have ha0 : p ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hc0 : p ^ 3 + 1 ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  have hpn2 : ¬ 2 ∣ p := by omega
  have hc2 : 2 ∣ p ^ 3 + 1 := by
    have : p ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hpodd]
    omega
  have hvz : padicValNat 2 (Nat.card (hypScalars h 1 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd hzodd
  have hvp : padicValNat 2 p = 0 := padicValNat.eq_zero_of_not_dvd hpn2
  have hv3 : 1 ≤ padicValNat 2 (p ^ 3 + 1) := one_le_padicValNat_of_dvd hc0 hc2
  have hab : p ^ 2 - 1 ≠ 0 := ha0
  have hv1 : padicValNat 2 (Nat.card (hypPSU h 1 1)) =
      padicValNat 2 (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) := by
    rw [← hPZ, padicValNat.mul hN0 hz0, hvz, add_zero]
  have hM : padicValNat 2 (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) =
      3 * 0 + (padicValNat 2 (p ^ 2 - 1) + padicValNat 2 (p ^ 3 + 1)) := by
    rw [padicValNat.mul (pow_ne_zero 3 hp0) (mul_ne_zero ha0 hc0), padicValNat.mul ha0 hc0,
      padicValNat.pow p 3, hvp]
  have hN : padicValNat 2 (p * (p ^ 2 - 1)) = padicValNat 2 (p ^ 2 - 1) := by
    rw [padicValNat.mul hp0 ha0, hvp, zero_add]
  have hle : padicValNat 2 (Nat.card (hypPSU h 1 1)) ≤ padicValNat 2 (p * (p ^ 2 - 1)) := by
    rw [hQ] at hdvd
    exact (padicValNat_dvd_iff_le (mul_ne_zero hp0 ha0)).1 hdvd
  rw [hv1, hM, hN] at hle
  omega

end CFSG.QuasithinUnique.Ch1
