module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open CFSG.Open

theorem padicValNat_card_statedProj_statedSL {K : Type} [Field K] [Finite K] {p m a : ℕ}
    (hp : p.Prime) (hm : 1 ≤ m) (hK : Nat.card K = p ^ m) (ha : 1 ≤ a) :
    padicValNat p (Nat.card (StatedProj (StatedSL a K))) = m * (a * (a - 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL ha, hK]
  have hq0 : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq1 : 1 < p ^ m := Nat.one_lt_pow (by omega) hp.one_lt
  have hf_ne : ∀ j ∈ Finset.Icc 2 a, (p ^ m) ^ j - 1 ≠ 0 := fun j hj =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by have := (Finset.mem_Icc.1 hj).1; omega) hq1)
  have hprod0 : (∏ j ∈ Finset.Icc 2 a, ((p ^ m) ^ j - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 hf_ne
  have hpq : p ∣ p ^ m := dvd_pow_self p (by omega)
  have hg_dvd : Nat.gcd a (p ^ m - 1) ∣
      (p ^ m) ^ (a * (a - 1) / 2) * (∏ j ∈ Finset.Icc 2 a, ((p ^ m) ^ j - 1)) := by
    rcases eq_or_lt_of_le ha with rfl | ha2
    · simp
    · have h1 : Nat.gcd a (p ^ m - 1) ∣ p ^ m - 1 := Nat.gcd_dvd_right _ _
      have h2 : p ^ m - 1 ∣ (p ^ m) ^ 2 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (p ^ m) 1 2
      have h3 : (p ^ m) ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 a, ((p ^ m) ^ j - 1) :=
        Finset.dvd_prod_of_mem (fun j => (p ^ m) ^ j - 1)
          (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
      exact ((h1.trans h2).trans h3).mul_left _
  rw [padicValNat.div_of_dvd hg_dvd]
  have hnotdvd : ∀ j ∈ Finset.Icc 2 a, ¬ p ∣ (p ^ m) ^ j - 1 := by
    intro j hj hpj
    have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.1 hj).1; omega
    have hpj' : p ∣ (p ^ m) ^ j := hpq.trans (dvd_pow_self (p ^ m) hj1)
    have h1 : p ∣ (p ^ m) ^ j - ((p ^ m) ^ j - 1) := Nat.dvd_sub hpj' hpj
    rw [Nat.sub_sub_self (Nat.one_le_pow j (p ^ m) (pow_pos hp.pos m))] at h1
    have hp2 : 2 ≤ p := hp.two_le
    have := Nat.le_of_dvd (by norm_num : 0 < 1) h1
    omega
  have hprod_v : padicValNat p (∏ j ∈ Finset.Icc 2 a, ((p ^ m) ^ j - 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd
      ((Nat.prime_iff.mp hp).not_dvd_finsetProd (g := fun j => (p ^ m) ^ j - 1) hnotdvd)
  have hg_v : padicValNat p (Nat.gcd a (p ^ m - 1)) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun h => ?_
    have hgd : p ∣ p ^ m - 1 := h.trans (Nat.gcd_dvd_right a (p ^ m - 1))
    have h1 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub hpq hgd
    rw [Nat.sub_sub_self (Nat.one_le_pow m p hp.pos)] at h1
    have hp2 : 2 ≤ p := hp.two_le
    have := Nat.le_of_dvd (by norm_num : 0 < 1) h1
    omega
  rw [padicValNat.mul (pow_ne_zero _ hq0) hprod0, hprod_v, hg_v, ← pow_mul,
    padicValNat.prime_pow]
  omega

theorem eq_two_of_mul_eq_twenty {n k : ℕ} (hn : n % 4 = 2) (h : n * (k * (k - 1) / 2) = 20) :
    n = 2 ∧ k = 5 := by
  have hn2 : 2 ≤ n := by omega
  have hX : k * (k - 1) / 2 ≤ 10 := by nlinarith [h, hn2]
  have hk : k ≤ 7 := by
    by_contra hk
    push Not at hk
    have h1 : 28 ≤ k * (k - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have hk1 : 7 ≤ k - 1 := by omega
      nlinarith
    omega
  interval_cases k <;> omega

theorem eq_ten_of_mul_eq_twenty {n a : ℕ} (hn : n % 4 = 2) (h : (2 * n) * (a * (a - 1) / 2) = 20) :
    n = 10 ∧ a = 2 := by
  have hn2 : 2 ≤ n := by omega
  have hX : a * (a - 1) / 2 ≤ 5 := by nlinarith [h, hn2]
  have ha : a ≤ 3 := by
    by_contra ha
    push Not at ha
    have h1 : 6 ≤ a * (a - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have ha1 : 3 ≤ a - 1 := by omega
      nlinarith
    omega
  interval_cases a <;> omega

theorem card_statedProj_statedSL_two_ne {K K₅ : Type} [Field K] [Finite K] [Field K₅] [Finite K₅]
    (hK : Nat.card K = 2 ^ 20) (hK₅ : Nat.card K₅ = (2 ^ 2) ^ 2) :
    Nat.card (StatedProj (StatedSL 2 K)) ≠ Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) := by
  have hL : Nat.card (StatedProj (StatedSL 2 K)) = 2 ^ 20 * (2 ^ 40 - 1) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hK,
      show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide]
    simp
  have hR : Nat.card (StatedProj (StatedSU 5 (2 ^ 2) K₅)) = 2 ^ 20 * 50968125 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 2) (n := 5)
      Nat.prime_two (by norm_num) hK₅ (by norm_num)]
    have hprod : (∏ i ∈ Finset.Icc 2 5, (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
        254840625 := by decide
    rw [hprod]
    norm_num
  rw [hL, hR]
  norm_num

end CFSG.LieType.SemisimpleCentralizers.OrderThree
