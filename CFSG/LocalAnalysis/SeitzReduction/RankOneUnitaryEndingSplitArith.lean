module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Twist

public section

namespace CFSG.SeitzReduction.RankOne

section NormWeight

theorem eq_zero_f_of_dvd_two_pow_add_two_pow {f i j m : ℕ} (hf : 2 ≤ f) (hi : i < 2 * f)
    (hj : j < 2 * f) (hm : m = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (h₁ : m ∣ 2 ^ i + 2 ^ j - (2 ^ f + 1)) (h₂ : m ∣ (2 ^ f + 1) - (2 ^ i + 2 ^ j)) :
    (i = 0 ∧ j = f) ∨ (i = f ∧ j = 0) := by
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set Q2 := q ^ 2 with hQ2
  have hQ2q : Q2 = q * q := sq q
  have hqq : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq4
  have hg : Nat.gcd 3 (q + 1) = 1 ∨ Nat.gcd 3 (q + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1))
  have hgdvd : Nat.gcd 3 (q + 1) ∣ Q2 - 1 := by
    refine (Nat.gcd_dvd_right 3 (q + 1)).trans ⟨q - 1, ?_⟩
    rw [hQ2q]
    have h1 : 1 ≤ q := by omega
    zify [h1, show 1 ≤ q * q by nlinarith]
    ring
  have hmg : m * Nat.gcd 3 (q + 1) = Q2 - 1 := by
    rw [hm]
    exact Nat.div_mul_cancel hgdvd
  have hi' : 2 ^ i ≤ 2 ^ (2 * f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (2 * f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2f : Q2 = 2 * 2 ^ (2 * f - 1) := by
    rw [hQ2, hq, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have h1i : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h1j : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h3m : Q2 - 1 ≤ 3 * m := by
    rcases hg with hg | hg <;> rw [hg] at hmg <;> omega
  rcases Nat.lt_trichotomy (2 ^ i + 2 ^ j) (q + 1) with hlt | heq | hgt
  · exfalso
    have hpos : 0 < q + 1 - (2 ^ i + 2 ^ j) := by omega
    have := Nat.le_of_dvd hpos h₂
    omega
  ·
    rcases i with _ | i
    · left
      refine ⟨rfl, Nat.pow_right_injective le_rfl ?_⟩
      simp only [pow_zero] at heq
      show 2 ^ j = 2 ^ f
      omega
    · rcases j with _ | j
      · right
        refine ⟨Nat.pow_right_injective le_rfl ?_, rfl⟩
        simp only [pow_zero] at heq
        show 2 ^ (i + 1) = 2 ^ f
        omega
      · exfalso
        have hf1 : q = 2 * 2 ^ (f - 1) := by
          rw [hq, ← pow_succ']
          congr 1
          omega
        rw [pow_succ, pow_succ] at heq
        omega
  · exfalso
    obtain ⟨k, hk⟩ := h₁
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    rcases hg with hg | hg
    · rw [hg, mul_one] at hmg
      have : m * 1 ≤ m * k := Nat.mul_le_mul_left m (by omega)
      omega
    ·
      rw [hg] at hmg
      have hf3 : 3 ≤ f := by
        by_contra hf3
        have hf2 : f = 2 := by omega
        rw [hf2] at hq
        rw [hq] at hg
        norm_num at hg
      set c := 2 ^ (f - 3) with hc
      have hq8 : q = 8 * c := by
        rw [hq, hc, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        congr 1
        omega
      have hQ2c : Q2 = 64 * (c * c) := by
        rw [hQ2q, hq8]
        ring
      have hk2 : k ≤ 2 := by
        by_contra hk3
        have : m * 3 ≤ m * k := Nat.mul_le_mul_left m (by omega)
        omega
      rcases two_pow_eq_or_eq_eight_mul i with hx | hx | hx | ⟨a, hx⟩ <;>
      rcases two_pow_eq_or_eq_eight_mul j with hy | hy | hy | ⟨b, hy⟩ <;>
      interval_cases k <;> omega

variable {K : Type*} [Field K] [Fintype K]

theorem eq_mul_trace_of_alternating_equivariant {f : ℕ} (hf : 2 ≤ f)
    (hK : Fintype.card K = (2 ^ f) ^ 2) (β : K →+ K →+ K) {μ : K} (hμ0 : μ ≠ 0)
    (hμ : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (hβ : ∀ a b, β (μ * a) (μ * b) = μ ^ (2 ^ f + 1) * β a b) (halt : ∀ a, β a a = 0) :
    ∃ c : K, ∀ a b, β a b = c * (a * b ^ 2 ^ f + a ^ 2 ^ f * b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Fintype.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [Nat.card_eq_fintype_card, hK']
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  obtain ⟨-, hb, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases Nat.prime_two
      (n := 2 * f) (by omega) hcard
  obtain ⟨c, hc, -⟩ := hb β
  have hlt : 2 ^ (2 * f - 1) < Fintype.card K := by
    rw [hK']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcoef : ∀ i j : Fin (2 * f),
      c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = c i j * μ ^ (2 ^ f + 1) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) - c i j * μ ^ (2 ^ f + 1))
      fun u w => by
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
          _ = μ ^ (2 ^ f + 1) * ∑ i, ∑ j, c i j * (u ^ 2 ^ (i : ℕ) * w ^ 2 ^ (j : ℕ)) := h1
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
    intro i j
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hzero : ∀ i j : Fin (2 * f),
      ¬ (((i : ℕ) = 0 ∧ (j : ℕ) = f) ∨ ((i : ℕ) = f ∧ (j : ℕ) = 0)) → c i j = 0 := by
    intro i j hij
    by_contra hcij
    have h1 := mul_left_cancel₀ hcij (hcoef i j)
    apply hij
    refine eq_zero_f_of_dvd_two_pow_add_two_pow hf i.2 j.2 hμ ?_ ?_
    · rcases Nat.lt_or_ge (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) (2 ^ f + 1) with hlt' | hge
      · rw [Nat.sub_eq_zero_of_le hlt'.le]
        exact dvd_zero _
      · apply orderOf_dvd_of_pow_eq_one
        have e : μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
            μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ) - (2 ^ f + 1)) * μ ^ (2 ^ f + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hge]
        rw [e] at h1
        exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1.trans (one_mul _).symm)
    · rcases Nat.lt_or_ge (2 ^ f + 1) (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) with hlt' | hge
      · rw [Nat.sub_eq_zero_of_le hlt'.le]
        exact dvd_zero _
      · apply orderOf_dvd_of_pow_eq_one
        have e : μ ^ (2 ^ f + 1) =
            μ ^ (2 ^ f + 1 - (2 ^ (i : ℕ) + 2 ^ (j : ℕ))) * μ ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) := by
          rw [← pow_add, Nat.sub_add_cancel hge]
        rw [e] at h1
        exact mul_right_cancel₀ (pow_ne_zero _ hμ0) (h1.symm.trans (one_mul _).symm)
  set i0 : Fin (2 * f) := ⟨0, by omega⟩ with hi0
  set iF : Fin (2 * f) := ⟨f, by omega⟩ with hiF
  have hne : i0 ≠ iF := by
    intro h
    have := congrArg Fin.val h
    simp only [hi0, hiF] at this
    omega
  have hval : ∀ a b, β a b = c i0 iF * (a * b ^ 2 ^ f) + c iF i0 * (a ^ 2 ^ f * b) := by
    intro a b
    rw [hc a b]
    rw [Fintype.sum_eq_add i0 iF hne (fun i hi => Finset.sum_eq_zero fun j _ => by
      rw [hzero i j (by
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hi.1 (Fin.ext h1)
        · exact hi.2 (Fin.ext h1)), zero_mul])]
    rw [Finset.sum_eq_single iF (fun j _ hj => by
        rw [hzero i0 j (by
          rintro (⟨-, h1⟩ | ⟨h1, -⟩)
          · exact hj (Fin.ext h1)
          · simp only [hi0] at h1
            omega), zero_mul]) (by simp),
      Finset.sum_eq_single i0 (fun j _ hj => by
        rw [hzero iF j (by
          rintro (⟨h1, -⟩ | ⟨-, h1⟩)
          · simp only [hiF] at h1
            omega
          · exact hj (Fin.ext h1)), zero_mul]) (by simp)]
    simp only [hi0, hiF, pow_zero, pow_one]
  have hsum : c iF i0 = c i0 iF := by
    have h1 := halt 1
    rw [hval] at h1
    simp only [one_pow, mul_one] at h1
    have h2 : c iF i0 = -c i0 iF := by linear_combination h1
    rw [h2, CharTwo.neg_eq]
  refine ⟨c i0 iF, fun a b => ?_⟩
  rw [hval, hsum]
  ring

theorem card_filter_pow_eq_self_le [DecidableEq K] {q : ℕ} (hq : 1 < q) :
    (Finset.univ.filter fun x : K => x ^ q = x).card ≤ q := by
  classical
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  calc (Finset.univ.filter fun x : K => x ^ q = x).card
      ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        simp [hx.2]
    _ ≤ Multiset.card (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial K).natDegree := Polynomial.card_roots' _
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq

end NormWeight

end CFSG.SeitzReduction.RankOne
