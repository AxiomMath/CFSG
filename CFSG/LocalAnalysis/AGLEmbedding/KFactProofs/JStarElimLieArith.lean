module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem dvd_of_ppd_dvd_pow_sub_one {p k j ℓ : ℕ} (hk : 0 < k) (hℓ : ℓ ∣ p ^ k - 1)
    (hprim : ∀ i : ℕ, 0 < i → i < k → ¬ ℓ ∣ p ^ i - 1) (hj : ℓ ∣ p ^ j - 1) : k ∣ j := by
  have hg : ℓ ∣ p ^ (Nat.gcd k j) - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hℓ hj
  by_contra hkj
  have hgk : Nat.gcd k j < k :=
    lt_of_le_of_ne (Nat.gcd_le_left _ hk) (fun h => hkj (h ▸ Nat.gcd_dvd_right k j))
  exact hprim _ (Nat.gcd_pos_of_pos_left _ hk) hgk hg

theorem exists_ppd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ p ∧ ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ k ∣ j := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) hp3 (n := k) hk
  refine ⟨ℓ, hℓ, ?_, ?_, fun j => ⟨dvd_of_ppd_dvd_pow_sub_one (by omega) hℓd hprim, fun hkj => ?_⟩⟩
  · rintro rfl
    exact hprim 1 one_pos (by omega) (by simpa using (hp.even_sub_one hp2).two_dvd)
  · rintro rfl
    have h1 : ℓ ∣ ℓ ^ k := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  · obtain ⟨c, rfl⟩ := hkj
    rw [pow_mul]
    exact hℓd.trans (by simpa using Nat.sub_dvd_pow_sub_pow (p ^ k) 1 c)

theorem ppd_ne_three {p k ℓ : ℕ} (hp : p.Prime) (hℓp : ℓ ≠ p) (hk : 3 ≤ k)
    (h : ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ k ∣ j) : ℓ ≠ 3 := by
  rintro rfl
  have h3 : ¬ 3 ∣ p := fun h' => hℓp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h')
  have hpp : p * p % 3 = 1 := by
    rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h <;> simp [Nat.mul_mod, h]
  have : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (by have := hp.pos; positivity)
  have h2 : 3 ∣ p ^ 2 - 1 := by rw [sq]; omega
  have := (h 2).mp h2
  have := Nat.le_of_dvd (by omega) this
  omega


theorem lt_add_of_pow_dvd_pow_mul {p x y m : ℕ} (hp : 2 ≤ p) (hm : 0 < m)
    (h : p ^ x ∣ p ^ y * m) : x < y + m := by
  by_cases hxy : x ≤ y
  · omega
  · push Not at hxy
    have h1 : p ^ y * p ^ (x - y) ∣ p ^ y * m := by
      rwa [← pow_add, show y + (x - y) = x by omega]
    have h2 : p ^ (x - y) ∣ m := (Nat.mul_dvd_mul_iff_left (pow_pos (by omega) y)).mp h1
    have h3 : p ^ (x - y) ≤ m := Nat.le_of_dvd hm h2
    have h4 : m < p ^ m := Nat.lt_pow_self (by omega)
    have h5 : p ^ (x - y) < p ^ m := lt_of_le_of_lt h3 h4
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp h5
    omega

theorem pow_dvd_of_pow_dvd_pow_mul_coprime {p x y c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c)
    (h : p ^ x ∣ p ^ y * c) : x ≤ y := by
  have hcop : Nat.Coprime (p ^ x) c :=
    Nat.Coprime.pow_left x ((Nat.Prime.coprime_iff_not_dvd hp).mpr hc)
  have h1 : p ^ x ∣ p ^ y := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1

theorem two_mul_half_sq_sub_one {q : ℕ} (hq : Odd q) : 2 * ((q ^ 2 - 1) / 2) = q ^ 2 - 1 :=
  Nat.mul_div_cancel' (Nat.Odd.sub_odd hq.pow odd_one).two_dvd

theorem dvd_pow_sub_one_of_dvd_psl_order {p m ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (h : ℓ ∣ p ^ m * (((p ^ m) ^ 2 - 1) / 2)) :
    ℓ ∣ p ^ (2 * m) - 1 := by
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h1
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h1)) hℓp
  · have : ℓ ∣ (p ^ m) ^ 2 - 1 := by
      rw [← two_mul_half_sq_sub_one hodd]
      exact h1.mul_left 2
    rwa [← pow_mul, mul_comm] at this

theorem dvd_psl_order_of_dvd_pow_sub_one {p m ℓ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (h : ℓ ∣ p ^ (2 * m) - 1) :
    ℓ ∣ p ^ m * (((p ^ m) ^ 2 - 1) / 2) := by
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have h1 : ℓ ∣ 2 * (((p ^ m) ^ 2 - 1) / 2) := by
    rw [two_mul_half_sq_sub_one hodd, ← pow_mul, mul_comm]
    exact h
  exact Dvd.dvd.mul_left (((Nat.Prime.dvd_mul hℓ).mp h1).resolve_left
    fun h2 => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)) _

theorem le_of_pow_dvd_psl_order {p m j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h : p ^ j ∣ p ^ m * (((p ^ m) ^ 2 - 1) / 2)) : j ≤ m := by
  refine pow_dvd_of_pow_dvd_pow_mul_coprime hp ?_ h
  intro hdvd
  have h1 : p ∣ (p ^ m) ^ 2 - 1 := by
    rw [← two_mul_half_sq_sub_one ((hp.odd_of_ne_two hp2).pow)]
    exact hdvd.mul_left 2
  have h2 : p ∣ (p ^ m) ^ 2 := (dvd_pow_self p (by omega : m ≠ 0)).pow two_ne_zero
  have h3 := Nat.dvd_sub h2 h1
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos hp.pos m))] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)


theorem ordTwistedA_two_mul_gcd_eq (q : ℕ) (hq : 1 ≤ q) :
    ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, prod_toNat_icc_two_three q hq]
  have hg : Nat.gcd (2 + 1) (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    refine Dvd.dvd.mul_right ?_ _
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact ⟨k, by
      have h : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
      omega⟩
  rw [Nat.mul_div_assoc _ hg, mul_assoc, Nat.div_mul_cancel hg]

theorem dvd_sq_sub_one_of_dvd_add_one {x ℓ : ℕ} (h : ℓ ∣ x + 1) : ℓ ∣ x ^ 2 - 1 := by
  have := Nat.sq_sub_sq x 1
  rw [one_pow] at this
  rw [this]
  exact Dvd.dvd.mul_right h _

theorem dvd_pow_sub_one_of_dvd_ordTwistedA_two {p a ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) (h : ℓ ∣ ordTwistedA 2 (p ^ a)) :
    ℓ ∣ p ^ (2 * a) - 1 ∨ ℓ ∣ p ^ (6 * a) - 1 := by
  have h1 := ordTwistedA_two_mul_gcd_eq (p ^ a) (Nat.one_le_pow _ _ hp.pos)
  have h2 : ℓ ∣ (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)) := by
    rw [← h1]; exact Dvd.dvd.mul_right h _
  rcases (Nat.Prime.dvd_mul hℓ).mp h2 with h3 | h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow (hℓ.dvd_of_dvd_pow h3)))
      hℓp
  · rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
    · left; rwa [← pow_mul, mul_comm] at h4
    · right
      have h5 := dvd_sq_sub_one_of_dvd_add_one h4
      have e : ((p ^ a) ^ 3) ^ 2 = p ^ (6 * a) := by rw [← pow_mul, ← pow_mul]; ring_nf
      rwa [e] at h5

theorem dvd_ordTwistedA_two_of_dvd_cube_add_one {q ℓ : ℕ} (hq : 1 ≤ q) (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (h : ℓ ∣ q ^ 3 + 1) : ℓ ∣ ordTwistedA 2 q := by
  have h1 : ℓ ∣ ordTwistedA 2 q * Nat.gcd 3 (q + 1) := by
    rw [ordTwistedA_two_mul_gcd_eq q hq]
    exact (h.mul_left _).mul_left _
  rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
  · exact h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp
      (h2.trans (Nat.gcd_dvd_left _ _))) hℓ3

theorem le_of_pow_dvd_ordTwistedA_two {p a j : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : p ^ j ∣ ordTwistedA 2 (p ^ a)) : j ≤ 3 * a := by
  have h1 := ordTwistedA_two_mul_gcd_eq (p ^ a) (Nat.one_le_pow _ _ hp.pos)
  have h2 : p ^ j ∣ (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)) := by
    rw [← h1]; exact Dvd.dvd.mul_right h _
  have e : (p ^ a) ^ 3 = p ^ (3 * a) := by rw [← pow_mul, mul_comm]
  have e2 : (p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)) =
      p ^ (3 * a) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)) := congrArg (· * _) e
  rw [e2] at h2
  refine pow_dvd_of_pow_dvd_pow_mul_coprime hp ?_ h2
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
  · have h4 : p ∣ (p ^ a) ^ 2 := (dvd_pow_self p (by omega : a ≠ 0)).pow two_ne_zero
    have h5 := Nat.dvd_sub h4 h3
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos hp.pos a))] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  · have h4 : p ∣ (p ^ a) ^ 3 := (dvd_pow_self p (by omega : a ≠ 0)).pow three_ne_zero
    have h5 := (Nat.dvd_add_right h4).mp h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)


theorem not_psl_cube_dvd_ordTwistedA_two {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ q ^ 3 * (((q ^ 3) ^ 2 - 1) / 2) ∣ ordTwistedA 2 q := by
  intro hdvd
  set c := ((q ^ 3) ^ 2 - 1) / 2 with hc
  have h2c : 2 * c = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    rw [hc, two_mul_half_sq_sub_one hq.pow]
    have := Nat.sq_sub_sq (q ^ 3) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have hg := ordTwistedA_two_mul_gcd_eq q (by omega)
  have h1 : q ^ 3 * c * Nat.gcd 3 (q + 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [← hg]; exact Nat.mul_dvd_mul_right hdvd _
  have h2 : c * Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [mul_assoc] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have h3 : (2 * c) * Nat.gcd 3 (q + 1) ∣ 2 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [mul_assoc]; exact Nat.mul_dvd_mul_left 2 h2
  rw [h2c] at h3
  have h4 : (q ^ 3 - 1) * Nat.gcd 3 (q + 1) * (q ^ 3 + 1) ∣ 2 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have e1 : (q ^ 3 - 1) * Nat.gcd 3 (q + 1) * (q ^ 3 + 1) =
        (q ^ 3 - 1) * (q ^ 3 + 1) * Nat.gcd 3 (q + 1) := by ring
    have e2 : 2 * (q ^ 2 - 1) * (q ^ 3 + 1) = 2 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by ring
    rw [e1, e2]; exact h3
  have h5 := (Nat.mul_dvd_mul_iff_right (by positivity)).mp h4
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 := Nat.le_of_dvd (by
    have : 2 ≤ q ^ 2 := by nlinarith
    omega) h5
  have hgpos : 1 ≤ Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h7 : q ^ 3 - 1 ≤ 2 * (q ^ 2 - 1) := le_trans (Nat.le_mul_of_pos_right _ hgpos) h6
  have h8 : 3 * q ^ 2 ≤ q ^ 3 := by nlinarith
  have h9 : 4 ≤ q ^ 2 := by nlinarith
  omega

theorem not_ree_dvd_psl_cube {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ q ^ 3 * (q ^ 3 + 1) * (q - 1) ∣ q ^ 3 * (((q ^ 3) ^ 2 - 1) / 2) := by
  intro hdvd
  set c := ((q ^ 3) ^ 2 - 1) / 2 with hc
  have h2c : 2 * c = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    rw [hc, two_mul_half_sq_sub_one hq.pow]
    have := Nat.sq_sub_sq (q ^ 3) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have h1 : q ^ 3 * ((q ^ 3 + 1) * (q - 1)) ∣ q ^ 3 * c := by
    rwa [← mul_assoc]
  have h2 : (q ^ 3 + 1) * (q - 1) ∣ c := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have h3 : 2 * ((q ^ 3 + 1) * (q - 1)) ∣ (q ^ 3 - 1) * (q ^ 3 + 1) := by
    rw [← h2c]; exact Nat.mul_dvd_mul_left 2 h2
  have h4 : (2 * (q - 1)) * (q ^ 3 + 1) ∣ (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have e1 : (2 * (q - 1)) * (q ^ 3 + 1) = 2 * ((q ^ 3 + 1) * (q - 1)) := by ring
    rw [e1]; exact h3
  have h5 : 2 * (q - 1) ∣ q ^ 3 - 1 := (Nat.mul_dvd_mul_iff_right (by positivity)).mp h4
  have h6 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have h1q : 1 ≤ q := by omega
    have h1q3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [h1q, h1q3]
    ring
  rw [h6] at h5
  have h7 : 2 ∣ q ^ 2 + q + 1 := by
    have : 2 * (q - 1) = (q - 1) * 2 := by ring
    rw [this] at h5
    exact (Nat.mul_dvd_mul_iff_left (by omega)).mp h5
  obtain ⟨k, hk⟩ := hq
  subst hk
  have : (2 * k + 1) ^ 2 + (2 * k + 1) + 1 = 2 * (2 * k ^ 2 + 3 * k + 1) + 1 := by ring
  omega


theorem not_psl_cube_dvd_ree_order {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ q ^ 3 * (((q ^ 3) ^ 2 - 1) / 2) ∣ q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  intro hdvd
  set c := ((q ^ 3) ^ 2 - 1) / 2 with hc
  have h2c : 2 * c = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    rw [hc, two_mul_half_sq_sub_one hq.pow]
    have := Nat.sq_sub_sq (q ^ 3) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have h1 : q ^ 3 * c ∣ q ^ 3 * ((q ^ 3 + 1) * (q - 1)) := by rwa [← mul_assoc]
  have h2 : c ∣ (q ^ 3 + 1) * (q - 1) := (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have h3 : (q ^ 3 - 1) * (q ^ 3 + 1) ∣ 2 * ((q ^ 3 + 1) * (q - 1)) := by
    rw [← h2c]; exact Nat.mul_dvd_mul_left 2 h2
  have h4 : (q ^ 3 - 1) * (q ^ 3 + 1) ∣ (2 * (q - 1)) * (q ^ 3 + 1) := by
    have e1 : (2 * (q - 1)) * (q ^ 3 + 1) = 2 * ((q ^ 3 + 1) * (q - 1)) := by ring
    rw [e1]; exact h3
  have h5 : q ^ 3 - 1 ∣ 2 * (q - 1) := (Nat.mul_dvd_mul_iff_right (by positivity)).mp h4
  have h6 := Nat.le_of_dvd (by omega) h5
  have h8 : 3 * q ^ 2 ≤ q ^ 3 := by nlinarith
  have h9 : 9 ≤ q ^ 2 := by nlinarith
  have h10 : q ≤ q ^ 2 := by nlinarith
  omega

theorem not_ordTwistedA_two_dvd_psl_cube {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    ¬ ordTwistedA 2 q ∣ q ^ 3 * (((q ^ 3) ^ 2 - 1) / 2) := by
  intro hdvd
  set c := ((q ^ 3) ^ 2 - 1) / 2 with hc
  have h2c : 2 * c = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    rw [hc, two_mul_half_sq_sub_one hq.pow]
    have := Nat.sq_sub_sq (q ^ 3) 1
    rw [one_pow] at this
    rw [this, mul_comm]
  have hg := ordTwistedA_two_mul_gcd_eq q (by omega)
  have h1 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ q ^ 3 * c * Nat.gcd 3 (q + 1) := by
    rw [← hg]; exact Nat.mul_dvd_mul_right hdvd _
  have h2 : (q ^ 2 - 1) * (q ^ 3 + 1) ∣ c * Nat.gcd 3 (q + 1) := by
    rw [mul_assoc] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have h3 : 2 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ (q ^ 3 - 1) * (q ^ 3 + 1) * Nat.gcd 3 (q + 1) := by
    rw [← h2c, mul_assoc]; exact Nat.mul_dvd_mul_left 2 h2
  have h4 : (2 * (q ^ 2 - 1)) * (q ^ 3 + 1) ∣ ((q ^ 3 - 1) * Nat.gcd 3 (q + 1)) * (q ^ 3 + 1) := by
    have e1 : (2 * (q ^ 2 - 1)) * (q ^ 3 + 1) = 2 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by ring
    have e2 : ((q ^ 3 - 1) * Nat.gcd 3 (q + 1)) * (q ^ 3 + 1) =
        (q ^ 3 - 1) * (q ^ 3 + 1) * Nat.gcd 3 (q + 1) := by ring
    rw [e1, e2]; exact h3
  have h5 : 2 * (q ^ 2 - 1) ∣ (q ^ 3 - 1) * Nat.gcd 3 (q + 1) :=
    (Nat.mul_dvd_mul_iff_right (by positivity)).mp h4
  have h6 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1q : 1 ≤ q := by omega
    have h1q2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1q, h1q2]
    ring
  have h7 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have h1q : 1 ≤ q := by omega
    have h1q3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [h1q, h1q3]
    ring
  rw [h6, h7, ← mul_assoc, mul_assoc (q - 1)] at h5
  have h8 : 2 * (q + 1) ∣ (q ^ 2 + q + 1) * Nat.gcd 3 (q + 1) := by
    have e : 2 * (q - 1) * (q + 1) = (q - 1) * (2 * (q + 1)) := by ring
    rw [e] at h5
    exact (Nat.mul_dvd_mul_iff_left (by omega)).mp h5
  have h9 : 2 ∣ (q ^ 2 + q + 1) * Nat.gcd 3 (q + 1) := (dvd_mul_right 2 _).trans h8
  have hgodd : Odd (Nat.gcd 3 (q + 1)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  obtain ⟨k, hk⟩ := hq
  subst hk
  have h10 : Odd ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) :=
    ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
  have h11 := h10.mul hgodd
  exact (Nat.not_even_iff_odd.mpr h11) (even_iff_two_dvd.mpr h9)


theorem dvd_cube_add_one_of_ppd {p n ℓ : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (h : ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ 6 * n ∣ j) : ℓ ∣ (p ^ n) ^ 3 + 1 := by
  have h1 : ℓ ∣ ((p ^ n) ^ 3) ^ 2 - 1 := by
    have : ((p ^ n) ^ 3) ^ 2 = p ^ (6 * n) := by rw [← pow_mul, ← pow_mul]; ring_nf
    rw [this]
    exact (h _).mpr dvd_rfl
  have h2 := Nat.sq_sub_sq ((p ^ n) ^ 3) 1
  rw [one_pow] at h2
  rw [h2] at h1
  rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h3 | h3
  · exact h3
  · exfalso
    have : (p ^ n) ^ 3 = p ^ (3 * n) := by rw [← pow_mul, mul_comm]
    rw [this] at h3
    have := (h _).mp h3
    have := Nat.le_of_dvd (by omega) this
    omega

theorem dvd_of_dvd_ree_shape {q ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q)
    (h : ℓ ∣ q ^ 3 * (q ^ 3 + 1) * (q - 1)) : ℓ ∣ q ^ 3 + 1 ∨ ℓ ∣ q - 1 := by
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
    · exact absurd (hℓ.dvd_of_dvd_pow h2) hℓq
    · exact Or.inl h2
  · exact Or.inr h1

theorem not_psl_dvd_ordTwistedA_two {p a n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hn : 3 ≤ n) (hdvd : p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ ordTwistedA 2 (p ^ a))
    (hpb : p ^ (3 * a) ∣ p ^ n * n) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h3a : 3 * a < n + n := lt_add_of_pow_dvd_pow_mul hp.two_le (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd hp hp2 (k := 2 * n) (by omega)
  have hℓd : ℓ ∣ ordTwistedA 2 (p ^ a) :=
    (dvd_psl_order_of_dvd_pow_sub_one hp hp2 hℓ hℓ2 ((hppd _).mpr dvd_rfl)).trans hdvd
  rcases dvd_pow_sub_one_of_dvd_ordTwistedA_two hp hℓ hℓp hℓd with h | h
  · have h1 := Nat.le_of_dvd (by omega) ((hppd _).mp h)
    omega
  · obtain ⟨m, hm⟩ := (hppd _).mp h
    have hm1 : m = 1 := by
      rcases m with _ | _ | _ | m
      · omega
      · rfl
      · omega
      · nlinarith
    subst hm1
    have hna : n = 3 * a := by omega
    subst hna
    have e : p ^ (3 * a) = (p ^ a) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [e] at hdvd
    exact not_psl_cube_dvd_ordTwistedA_two ((hp.odd_of_ne_two hp2).pow)
      (le_trans hp3 (Nat.le_self_pow (by omega) p)) hdvd


theorem not_psl_dvd_ree_order {a n : ℕ} (ha : 1 ≤ a) (hn : 3 ≤ n)
    (hdvd : 3 ^ n * (((3 ^ n) ^ 2 - 1) / 2) ∣ (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * (3 ^ a - 1))
    (hpb : 3 ^ (3 * a) ∣ 3 ^ n * n) : False := by
  have h3a : 3 * a < n + n := lt_add_of_pow_dvd_pow_mul (by norm_num) (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd Nat.prime_three (by norm_num) (k := 2 * n)
    (by omega)
  have hℓd : ℓ ∣ (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * (3 ^ a - 1) :=
    (dvd_psl_order_of_dvd_pow_sub_one Nat.prime_three (by norm_num) hℓ hℓ2
      ((hppd _).mpr dvd_rfl)).trans hdvd
  have hℓ3a : ¬ ℓ ∣ 3 ^ a := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
  rcases dvd_of_dvd_ree_shape hℓ hℓ3a hℓd with h | h
  · have h5 := dvd_sq_sub_one_of_dvd_add_one h
    have e : ((3 ^ a) ^ 3) ^ 2 = 3 ^ (6 * a) := by rw [← pow_mul, ← pow_mul]; ring_nf
    rw [e] at h5
    obtain ⟨m, hm⟩ := (hppd _).mp h5
    have hm1 : m = 1 := by
      rcases m with _ | _ | _ | m
      · omega
      · rfl
      · omega
      · nlinarith
    subst hm1
    have hna : n = 3 * a := by omega
    subst hna
    have e' : 3 ^ (3 * a) = (3 ^ a) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [e'] at hdvd
    have h3q : 3 ≤ 3 ^ a := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    exact not_psl_cube_dvd_ree_order (q := 3 ^ a) ((by decide : Odd 3).pow) h3q hdvd
  · have h1 := Nat.le_of_dvd (by omega) ((hppd _).mp h)
    omega


theorem ordBC_two_mul_gcd (q : ℕ) :
    ordBC 2 q * Nat.gcd 2 (q - 1) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  unfold ordBC
  have h : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    refine Dvd.dvd.mul_right ?_ _
    refine (Nat.gcd_dvd_right _ _).trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  rw [Nat.div_mul_cancel hg]

theorem not_psl_dvd_ordBC_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hdvd : p ^ n * (((p ^ n) ^ 2 - 1) / 2) ∣ ordBC 2 p) : False := by
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd hp hp2 (k := 2 * n) (by omega)
  have hℓd : ℓ ∣ ordBC 2 p :=
    (dvd_psl_order_of_dvd_pow_sub_one hp hp2 hℓ hℓ2 ((hppd _).mpr dvd_rfl)).trans hdvd
  have h1 : ℓ ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
    rw [← ordBC_two_mul_gcd]; exact Dvd.dvd.mul_right hℓd _
  rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
  · exact hℓp (Nat.prime_dvd_prime_iff_eq hℓ hp |>.mp (hℓ.dvd_of_dvd_pow h2))
  · rcases (Nat.Prime.dvd_mul hℓ).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by omega) ((hppd 2).mp h3)
      omega
    · have := Nat.le_of_dvd (by omega) ((hppd 4).mp h3)
      omega


theorem le_of_pow_dvd_ordBC_two {p j : ℕ} (hp : p.Prime) (h : p ^ j ∣ ordBC 2 p) : j ≤ 4 := by
  have h1 : p ^ j ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
    rw [← ordBC_two_mul_gcd]; exact Dvd.dvd.mul_right h _
  refine pow_dvd_of_pow_dvd_pow_mul_coprime hp ?_ h1
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h2
  · have h3 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    have h4 := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  · have h3 : p ∣ p ^ 4 := dvd_pow_self p (by norm_num)
    have h4 := Nat.dvd_sub h3 h2
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

theorem le_of_pow_dvd_ree_shape {p a j : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : p ^ j ∣ (p ^ a) ^ 3 * ((p ^ a) ^ 3 + 1) * (p ^ a - 1)) : j ≤ 3 * a := by
  have e0 : (p ^ a) ^ 3 = p ^ (3 * a) := by rw [← pow_mul, mul_comm]
  have e : (p ^ a) ^ 3 * ((p ^ a) ^ 3 + 1) * (p ^ a - 1) =
      p ^ (3 * a) * (((p ^ a) ^ 3 + 1) * (p ^ a - 1)) := by
    rw [mul_assoc]; exact congrArg (· * _) e0
  rw [e] at h
  refine pow_dvd_of_pow_dvd_pow_mul_coprime hp ?_ h
  intro hdvd
  have hpa : p ∣ p ^ a := dvd_pow_self p (by omega)
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · have h2 : p ∣ (p ^ a) ^ 3 := hpa.pow (by norm_num)
    have := (Nat.dvd_add_right h2).mp h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · have h5 := Nat.dvd_sub hpa h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

theorem not_ordTwistedA_two_dvd_ree_shape {q : ℕ} (hq3 : 3 ≤ q) :
    ¬ ordTwistedA 2 q ∣ q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  intro hdvd
  have hg := ordTwistedA_two_mul_gcd_eq q (by omega)
  have h1 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣
      q ^ 3 * ((q ^ 3 + 1) * (q - 1)) * Nat.gcd 3 (q + 1) := by
    rw [← hg, ← mul_assoc]; exact Nat.mul_dvd_mul_right hdvd _
  have h2 : (q ^ 2 - 1) * (q ^ 3 + 1) ∣ (q ^ 3 + 1) * (q - 1) * Nat.gcd 3 (q + 1) := by
    rw [mul_assoc] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp h1
  have h3 : (q ^ 2 - 1) * (q ^ 3 + 1) ∣ (q - 1) * Nat.gcd 3 (q + 1) * (q ^ 3 + 1) := by
    have e : (q ^ 3 + 1) * (q - 1) * Nat.gcd 3 (q + 1) =
        (q - 1) * Nat.gcd 3 (q + 1) * (q ^ 3 + 1) := by ring
    rwa [e] at h2
  have h4 : q ^ 2 - 1 ∣ (q - 1) * Nat.gcd 3 (q + 1) :=
    (Nat.mul_dvd_mul_iff_right (by positivity)).mp h3
  have h6 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1q : 1 ≤ q := by omega
    have h1q2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1q, h1q2]
    ring
  rw [h6] at h4
  have h5 : q + 1 ∣ Nat.gcd 3 (q + 1) := (Nat.mul_dvd_mul_iff_left (by omega)).mp h4
  have h7 := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) h5
  have h8 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  omega

theorem not_ordTwistedA_two_dvd_ree_order {n a : ℕ} (hn : 2 ≤ n) (ha : 1 ≤ a)
    (hdvd : ordTwistedA 2 (3 ^ n) ∣ (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * (3 ^ a - 1))
    (hpb : 3 ^ (3 * a) ∣ 3 ^ (3 * n) * n) : False := by
  have hpn : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hna : n ≤ a := by
    have h1 : 3 ^ (3 * n) ∣ ordTwistedA 2 (3 ^ n) := by
      have := pow_dvd_ordTwistedA_two (3 ^ n) hpn
      rwa [← pow_mul, mul_comm] at this
    have := le_of_pow_dvd_ree_shape Nat.prime_three ha (h1.trans hdvd)
    omega
  have h3a : 3 * a < 3 * n + n := lt_add_of_pow_dvd_pow_mul (by norm_num) (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd Nat.prime_three (by norm_num) (k := 6 * n)
    (by omega)
  have hℓ3 : ℓ ≠ 3 := hℓp
  have hℓc : ℓ ∣ (3 ^ n) ^ 3 + 1 := dvd_cube_add_one_of_ppd hℓ (by omega) hppd
  have hℓd : ℓ ∣ (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * (3 ^ a - 1) :=
    (dvd_ordTwistedA_two_of_dvd_cube_add_one hpn hℓ hℓ3 hℓc).trans hdvd
  have hℓ3a : ¬ ℓ ∣ 3 ^ a := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
  rcases dvd_of_dvd_ree_shape hℓ hℓ3a hℓd with h | h
  · have h5 := dvd_sq_sub_one_of_dvd_add_one h
    have e : ((3 ^ a) ^ 3) ^ 2 = 3 ^ (6 * a) := by rw [← pow_mul, ← pow_mul]; ring_nf
    rw [e] at h5
    obtain ⟨j, hj⟩ := (hppd _).mp h5
    have hj1 : j = 1 := by
      rcases j with _ | _ | j
      · omega
      · rfl
      · nlinarith
    subst hj1
    have han : a = n := by omega
    subst han
    have h3q : 3 ≤ 3 ^ a := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    exact not_ordTwistedA_two_dvd_ree_shape h3q hdvd
  · have h1 := Nat.le_of_dvd (by omega) ((hppd _).mp h)
    omega


theorem not_ordTwistedA_two_dvd_psl {p n m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hdvd : ordTwistedA 2 (p ^ n) ∣ p ^ m * (((p ^ m) ^ 2 - 1) / 2))
    (hpb : p ^ m ∣ p ^ (3 * n) * n) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
  have h3n : 3 * n ≤ m := by
    have h1 : p ^ (3 * n) ∣ ordTwistedA 2 (p ^ n) := by
      have := pow_dvd_ordTwistedA_two (p ^ n) hpn
      rwa [← pow_mul, mul_comm] at this
    exact le_of_pow_dvd_psl_order hp hp2 hm (h1.trans hdvd)
  have hm4 : m < 3 * n + n := lt_add_of_pow_dvd_pow_mul hp.two_le (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd hp hp2 (k := 6 * n) (by omega)
  have hℓ3 : ℓ ≠ 3 := ppd_ne_three hp hℓp (by omega) hppd
  have hℓc : ℓ ∣ (p ^ n) ^ 3 + 1 := dvd_cube_add_one_of_ppd hℓ (by omega) hppd
  have hℓd : ℓ ∣ ordTwistedA 2 (p ^ n) :=
    dvd_ordTwistedA_two_of_dvd_cube_add_one hpn hℓ hℓ3 hℓc
  have hℓm : ℓ ∣ p ^ (2 * m) - 1 :=
    dvd_pow_sub_one_of_dvd_psl_order hp hp2 hℓ hℓp (hℓd.trans hdvd)
  obtain ⟨j, hj⟩ := (hppd _).mp hℓm
  have hj1 : j = 1 := by
    rcases j with _ | _ | j
    · omega
    · rfl
    · nlinarith
  subst hj1
  have hmn : m = 3 * n := by omega
  subst hmn
  have e : p ^ (3 * n) = (p ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [e] at hdvd
  exact not_ordTwistedA_two_dvd_psl_cube ((hp.odd_of_ne_two hp2).pow)
    (le_trans hp3 (Nat.le_self_pow (by omega) p)) hdvd

theorem not_ree_order_dvd_psl {n m : ℕ} (hn : 3 ≤ n) (hm : 1 ≤ m)
    (hdvd : (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) ∣ 3 ^ m * (((3 ^ m) ^ 2 - 1) / 2))
    (hpb : 3 ^ m ∣ 3 ^ (3 * n) * n) : False := by
  have hpn : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h3n : 3 * n ≤ m := by
    have h1 : 3 ^ (3 * n) ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm]) _) _
    exact le_of_pow_dvd_psl_order Nat.prime_three (by norm_num) hm (h1.trans hdvd)
  have hm4 : m < 3 * n + n := lt_add_of_pow_dvd_pow_mul (by norm_num) (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd Nat.prime_three (by norm_num) (k := 6 * n)
    (by omega)
  have hℓc : ℓ ∣ (3 ^ n) ^ 3 + 1 := dvd_cube_add_one_of_ppd hℓ (by omega) hppd
  have hℓd : ℓ ∣ 3 ^ m * (((3 ^ m) ^ 2 - 1) / 2) :=
    ((hℓc.mul_left _).mul_right _).trans hdvd
  have hℓm : ℓ ∣ 3 ^ (2 * m) - 1 :=
    dvd_pow_sub_one_of_dvd_psl_order Nat.prime_three (by norm_num) hℓ hℓp hℓd
  obtain ⟨j, hj⟩ := (hppd _).mp hℓm
  have hj1 : j = 1 := by
    rcases j with _ | _ | j
    · omega
    · rfl
    · nlinarith
  subst hj1
  have hmn : m = 3 * n := by omega
  subst hmn
  have e : 3 ^ (3 * n) = (3 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [e] at hdvd
  have h3q : 3 ≤ 3 ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact not_ree_dvd_psl_cube ((by decide : Odd 3).pow) h3q hdvd

theorem eq_of_ree_order_dvd_ordTwistedA_two {n a : ℕ} (hn : 3 ≤ n) (ha : 1 ≤ a)
    (hdvd : (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) ∣ ordTwistedA 2 (3 ^ a))
    (hpb : 3 ^ (3 * a) ∣ 3 ^ (3 * n) * n) : a = n := by
  have hna : n ≤ a := by
    have h1 : 3 ^ (3 * n) ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm]) _) _
    have := le_of_pow_dvd_ordTwistedA_two Nat.prime_three ha (h1.trans hdvd)
    omega
  have h3a : 3 * a < 3 * n + n := lt_add_of_pow_dvd_pow_mul (by norm_num) (by omega) hpb
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hppd⟩ := exists_ppd Nat.prime_three (by norm_num) (k := 6 * n)
    (by omega)
  have hℓc : ℓ ∣ (3 ^ n) ^ 3 + 1 := dvd_cube_add_one_of_ppd hℓ (by omega) hppd
  have hℓd : ℓ ∣ ordTwistedA 2 (3 ^ a) := ((hℓc.mul_left _).mul_right _).trans hdvd
  rcases dvd_pow_sub_one_of_dvd_ordTwistedA_two Nat.prime_three hℓ hℓp hℓd with h | h
  · have h1 := Nat.le_of_dvd (by omega) ((hppd _).mp h)
    omega
  · obtain ⟨j, hj⟩ := (hppd _).mp h
    have hj1 : j = 1 := by
      rcases j with _ | _ | j
      · omega
      · rfl
      · nlinarith
    subst hj1
    omega

@[expose] def chevThreeOrders : List ℕ :=
  [1451520, 47377612800, 13685760, 9196830720, 174182400, 3311126603366400,
    214841575522005575270400, 211341312, 1056706560, 4329310519296,
    19045158721552047314829312, 5515776]

@[expose] def reeFFiveOrder : ℕ := 1318633155799591447702161609782722560000

theorem chev3_nums :
    ordBC 3 (2 ^ 1) = 1451520 ∧ ordBC 4 (2 ^ 1) = 47377612800 ∧
    ordTwistedA 4 (2 ^ 1) = 13685760 ∧ ordTwistedA 5 (2 ^ 1) = 9196830720 ∧
    ordD 4 (2 ^ 1) = 174182400 ∧ ordF4 (2 ^ 1) = 3311126603366400 ∧
    ordE6 (2 ^ 1) = 214841575522005575270400 ∧ ordTrialityD4 (2 ^ 1) = 211341312 ∧
    ordBC 2 (2 ^ 3) = 1056706560 ∧ ordG2 (2 ^ 3) = 4329310519296 ∧
    ordTrialityD4 (2 ^ 3) = 19045158721552047314829312 ∧ ordTwistedA 2 (2 ^ 3) = 5515776 ∧
    ordTwistedF4 (2 ^ (2 * 2 + 1)) = reeFFiveOrder := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide


theorem not_three_pow_seven_dvd {N : ℕ} (hN : N ∈ chevThreeOrders) : ¬ 3 ^ 7 ∣ N := by
  simp only [chevThreeOrders, List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem chev_three_survivors_psl {N n : ℕ} (hN : N ∈ chevThreeOrders) (hn : 3 ≤ n)
    (h1 : 3 ^ n * (((3 ^ n) ^ 2 - 1) / 2) ∣ N) (h2 : ∀ k : ℕ, 3 ^ k ∣ N → 3 ^ k ∣ 3 ^ n * n) :
    (N = 211341312 ∧ n = 3) ∨ (N = 1056706560 ∧ n = 3) ∨
      (N = 214841575522005575270400 ∧ n = 6) := by
  have hn6 : n < 7 := by
    by_contra hcon
    push Not at hcon
    exact not_three_pow_seven_dvd hN
      ((pow_dvd_pow 3 hcon).trans ((Dvd.intro _ rfl).trans h1))
  have h2' : ∀ k < 10, 3 ^ k ∣ N → 3 ^ k ∣ 3 ^ n * n := fun k _ => h2 k
  clear h2
  simp only [chevThreeOrders, List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases n <;>
    first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | (exfalso; revert h1 h2'; decide)


theorem chev_three_survivors_unitary {N n : ℕ} (hN : N ∈ chevThreeOrders) (hn : 2 ≤ n)
    (h1 : ordTwistedA 2 (3 ^ n) ∣ N) :
    N = 214841575522005575270400 ∧ n = 2 := by
  have hn2 : n < 3 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 ^ (3 * n) ∣ ordTwistedA 2 (3 ^ n) := by
      have := pow_dvd_ordTwistedA_two (3 ^ n) (Nat.one_le_pow _ _ (by norm_num))
      rwa [← pow_mul, mul_comm] at this
    exact not_three_pow_seven_dvd hN ((pow_dvd_pow 3 (by omega)).trans (h3.trans h1))
  obtain rfl : n = 2 := by omega
  simp only [chevThreeOrders, List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨rfl, rfl⟩
    | (exfalso; revert h1; decide)

theorem not_three_pow_dvd_chev_three {N n : ℕ} (hN : N ∈ chevThreeOrders) (hn : 3 ≤ n)
    (h : 3 ^ (3 * n) ∣ N) : False :=
  not_three_pow_seven_dvd hN ((pow_dvd_pow 3 (by omega)).trans h)

theorem not_five_pow_five_dvd : ¬ 5 ^ 5 ∣ reeFFiveOrder := by decide

theorem not_psl_five_dvd_reeFFive {n : ℕ} (hn : 3 ≤ n)
    (h1 : 5 ^ n * (((5 ^ n) ^ 2 - 1) / 2) ∣ reeFFiveOrder)
    (h2 : ∀ k : ℕ, 5 ^ k ∣ reeFFiveOrder → 5 ^ k ∣ 5 ^ n * n) : False := by
  have hn5 : n < 5 := by
    by_contra hcon
    push Not at hcon
    exact not_five_pow_five_dvd ((pow_dvd_pow 5 hcon).trans ((Dvd.intro _ rfl).trans h1))
  have h2' : ∀ k < 10, 5 ^ k ∣ reeFFiveOrder → 5 ^ k ∣ 5 ^ n * n := fun k _ => h2 k
  clear h2
  interval_cases n <;> (revert h1 h2'; decide)

theorem not_five_pow_dvd_reeFFive {n : ℕ} (hn : 2 ≤ n) (h : 5 ^ (3 * n) ∣ reeFFiveOrder) :
    False :=
  not_five_pow_five_dvd ((pow_dvd_pow 5 (by omega)).trans h)

end CFSG.AGLEmbedding
