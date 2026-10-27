module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiTwist

public section

namespace CFSG.SeitzReduction.RankOne

section TwistOrder

variable {K : Type*} [Field K] [Fintype K]

theorem bilinear_eq_zero_of_alternating_equivariant_of_orderOf {n : ℕ}
    (hK : Fintype.card K = 2 ^ n) (β : K →+ K →+ K) {μ : K} (hμ0 : μ ≠ 0)
    (hμ : ∀ i j : ℕ, i < n → j < n → orderOf μ ∣ 2 ^ i + 2 ^ j - 1 → i = n - 1 ∧ j = n - 1)
    (hβ : ∀ u w, β (μ * u) (μ * w) = μ * β u w) (halt : ∀ u, β u u = 0) : β = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      rw [pow_zero] at hK
      exact absurd hK (Fintype.one_lt_card (α := K)).ne'
    · exact h
  have hcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨-, hb, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases Nat.prime_two hn hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i j : Fin n,
      c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = c i j * μ := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) - c i j * μ) fun u w => by
        have h1 := hβ u w
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        calc ∑ i, ∑ j, c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) *
              (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) =
            ∑ i, ∑ j, c i j * ((μ * u) ^ 2 ^ (i : ℕ) * (μ * w) ^ 2 ^ (j : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [mul_pow, mul_pow, pow_add]
              ring
          _ = μ * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hzero : ∀ i j : Fin n, ((i : ℕ) ≠ n - 1 ∨ (j : ℕ) ≠ n - 1) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    have h1i : 1 ≤ 2 ^ (i : ℕ) := Nat.one_le_two_pow
    have h1j : 1 ≤ 2 ^ (j : ℕ) := Nat.one_le_two_pow
    have hE : μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) = 1 := by
      rw [show 2 ^ (i : ℕ) + 2 ^ (j : ℕ) = (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1) + 1 by omega,
        pow_succ] at h1
      exact mul_right_cancel₀ hμ0 (h1.trans (one_mul μ).symm)
    have := hμ i j i.2 j.2 (orderOf_dvd_of_pow_eq_one hE)
    omega
  have hlast : c ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩ = 0 := by
    have h1 := halt 1
    rw [hc] at h1
    simp only [one_pow, mul_one] at h1
    rwa [Finset.sum_eq_single ⟨n - 1, by omega⟩ (fun i _ hi => Finset.sum_eq_zero fun j _ =>
      hzero i j (Or.inl fun h => hi (Fin.ext h))) (by simp),
      Finset.sum_eq_single ⟨n - 1, by omega⟩ (fun j _ hj =>
      hzero _ j (Or.inr fun h => hj (Fin.ext h))) (by simp)] at h1
  have hall : ∀ i j : Fin n, c i j = 0 := by
    intro i j
    by_cases hij : (i : ℕ) = n - 1 ∧ (j : ℕ) = n - 1
    · obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      obtain ⟨rfl, rfl⟩ := hij
      exact hlast
    · exact hzero i j (by tauto)
  refine AddMonoidHom.ext fun u => AddMonoidHom.ext fun w => ?_
  rw [hc]
  simp [hall]

theorem two_pow_eq_or_eq_eight_mul (i : ℕ) :
    2 ^ i = 1 ∨ 2 ^ i = 2 ∨ 2 ^ i = 4 ∨ ∃ a : ℕ, 2 ^ i = 8 * a := by
  rcases Nat.lt_or_ge i 3 with hi | hi
  · interval_cases i <;> simp
  · refine Or.inr (Or.inr (Or.inr ⟨2 ^ (i - 3), ?_⟩))
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega

theorem eq_of_dvd_two_pow_add_two_pow_sub_one_of_three_le {n i j : ℕ} (hn : 3 ≤ n)
    (hi : i < 2 * n) (hj : j < 2 * n) (h : (4 ^ n - 1) / 3 ∣ 2 ^ i + 2 ^ j - 1) :
    i = 2 * n - 1 ∧ j = 2 * n - 1 := by
  set m := (4 ^ n - 1) / 3 with hm
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have h64 : (4 : ℕ) ^ n = 64 * 4 ^ (n - 3) := by
    rw [show (64 : ℕ) = 4 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  have h3 : 3 ∣ 4 ^ n - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  have h4pos : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h3m : 3 * m + 1 = 4 ^ n := by
    rw [hm, Nat.mul_div_cancel' h3]
    omega
  set c := 4 ^ (n - 3) with hc
  have hc1 : 1 ≤ c := Nat.one_le_pow _ _ (by norm_num)
  have hi' : 2 ^ i ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2n : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1i : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ := h
  have hk3 : k ≤ 3 := by
    by_contra hk4
    push Not at hk4
    have : m * 4 ≤ m * k := Nat.mul_le_mul_left m hk4
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  rcases two_pow_eq_or_eq_eight_mul i with hx | hx | hx | ⟨a, hx⟩ <;>
  rcases two_pow_eq_or_eq_eight_mul j with hy | hy | hy | ⟨b, hy⟩ <;>
  interval_cases k <;>
  first
  | omega
  |
    have hsum : 2 ^ i + 2 ^ j = 2 ^ (2 * n) := by omega
    have hij := SzCoords.eq_of_two_pow_add_two_pow hsum
    subst hij
    have := SzCoords.eq_succ_of_two_pow_add_self hsum
    omega

theorem bilinear_eq_zero_of_alternating_equivariant_of_dvd_orderOf {n : ℕ} (hn : 3 ≤ n)
    (hK : Fintype.card K = 4 ^ n) (β : K →+ K →+ K) {μ : K} (hμ0 : μ ≠ 0)
    (hμ : (4 ^ n - 1) / 3 ∣ orderOf μ) (hβ : ∀ u w, β (μ * u) (μ * w) = μ * β u w)
    (halt : ∀ u, β u u = 0) : β = 0 := by
  have hK' : Fintype.card K = 2 ^ (2 * n) := by rw [hK, pow_mul]; norm_num
  exact bilinear_eq_zero_of_alternating_equivariant_of_orderOf hK' β hμ0
    (fun i j hi hj hdvd => eq_of_dvd_two_pow_add_two_pow_sub_one_of_three_le hn hi hj
      (hμ.trans hdvd)) hβ halt

theorem div_three_dvd_div_gcd_three (n : ℕ) :
    (4 ^ n - 1) / 3 ∣ ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) := by
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have h3 : 3 ∣ 4 ^ n - 1 := by simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (2 ^ n + 1)) with hg | hg
  · rw [hg, Nat.div_one]
    exact Nat.div_dvd_of_dvd h3
  · rw [hg]

theorem bilinear_eq_zero_of_alternating_equivariant_of_unitary_cartan {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = (2 ^ n) ^ 2) (β : K →+ K →+ K) {μ : K} (hμ0 : μ ≠ 0)
    (hμ : orderOf μ = ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1))
    (hβ : ∀ u w, β (μ * u) (μ * w) = μ * β u w) (halt : ∀ u, β u u = 0) : β = 0 := by
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hμ15 : orderOf μ = 2 ^ 4 - 1 := by rw [hμ]; norm_num
    have hK' : Fintype.card K = 2 ^ 4 := by rw [hK]; norm_num
    exact bilinear_eq_zero_of_alternating_equivariant_of_orderOf hK' β hμ0
      (fun i j hi hj hdvd => by
        rw [hμ15] at hdvd
        exact eq_pred_of_dvd_two_pow_add_two_pow_sub_one hi hj hdvd) hβ halt
  · have hK' : Fintype.card K = 4 ^ n := by
      rw [hK, ← pow_mul, mul_comm, pow_mul]; norm_num
    exact bilinear_eq_zero_of_alternating_equivariant_of_dvd_orderOf hn3 hK' β hμ0
      (by rw [hμ]; exact div_three_dvd_div_gcd_three n) hβ halt

end TwistOrder

end CFSG.SeitzReduction.RankOne
