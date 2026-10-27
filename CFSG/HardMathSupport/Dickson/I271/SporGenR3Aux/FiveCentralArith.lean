module

public import CFSG.Open.MonsterDefs

public section

namespace CFSG.HardMathSupport.Dickson.I271.FiveCentralArith

open CFSG.Open

theorem prime_dvd_monsterOrder {p : ℕ} (hp : p.Prime) (h : p ∣ monsterOrder) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨
      p = 31 ∨ p = 41 ∨ p = 47 ∨ p = 59 ∨ p = 71 := by
  have hq : ∀ q k : ℕ, q.Prime → p ∣ q ^ k → p = q := fun q k hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  unfold monsterOrder at h
  simp only [hp.dvd_mul] at h
  rcases h with
    ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  all_goals first
    | (have := hq 2 46 Nat.prime_two h; omega)
    | (have := hq 3 20 Nat.prime_three h; omega)
    | (have := hq 5 9 Nat.prime_five h; omega)
    | (have := hq 7 6 (by norm_num) h; omega)
    | (have := hq 11 2 (by norm_num) h; omega)
    | (have := hq 13 3 (by norm_num) h; omega)
    | (have := hq 17 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 19 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 23 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 29 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 31 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 41 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 47 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 59 1 (by norm_num) (by simpa using h); omega)
    | (have := hq 71 1 (by norm_num) (by simpa using h); omega)

theorem prime_two_or_three_of_pow_ten_dvd {p k : ℕ} (hp : p.Prime) (hk : 10 ≤ k)
    (h : p ^ k ∣ monsterOrder) : p = 2 ∨ p = 3 := by
  have hpM : p ∣ monsterOrder := (dvd_pow_self p (by omega)).trans h
  have h10 : p ^ 10 ∣ monsterOrder := (pow_dvd_pow p hk).trans h
  rcases prime_dvd_monsterOrder hp hpM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  all_goals (exfalso; revert h10; unfold monsterOrder; norm_num)

theorem le_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ monsterOrder) : k ≤ 46 := by
  by_contra hk
  have h47 : 2 ^ 47 ∣ monsterOrder := (pow_dvd_pow 2 (by omega)).trans h
  revert h47
  unfold monsterOrder
  norm_num

theorem le_of_three_pow_dvd {k : ℕ} (h : 3 ^ k ∣ monsterOrder) : k ≤ 20 := by
  by_contra hk
  have h21 : 3 ^ 21 ∣ monsterOrder := (pow_dvd_pow 3 (by omega)).trans h
  revert h21
  unfold monsterOrder
  norm_num

theorem pow_dvd_mul_div {q a P d : ℕ} (hd : d ∣ P) : q ^ a ∣ q ^ a * P / d := by
  rw [Nat.mul_div_assoc _ hd]
  exact dvd_mul_right _ _

theorem pow_dvd_ordA {q n : ℕ} (hn : 1 ≤ n) : q ^ (n * (n + 1) / 2) ∣ ordA n q := by
  unfold ordA
  refine pow_dvd_mul_div ((Nat.gcd_dvd_right _ _).trans
    ((Nat.sub_one_dvd_pow_sub_one q 2).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

theorem succ_dvd_toNat_sq (q : ℕ) : q + 1 ∣ ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat := by
  rcases q with _ | q
  · simp
  · refine ⟨q, ?_⟩
    have : (((q + 1 : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = (((q + 1 + 1) * q : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]

theorem pow_dvd_ordTwistedA {q n : ℕ} (hn : 1 ≤ n) :
    q ^ (n * (n + 1) / 2) ∣ ordTwistedA n q := by
  unfold ordTwistedA
  refine pow_dvd_mul_div ((Nat.gcd_dvd_right _ _).trans
    ((succ_dvd_toNat_sq q).trans ?_))
  exact Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)

theorem bound_of_pow_dvd {p k : ℕ} (hp : p.Prime) (hk : 10 ≤ k) (h : p ^ k ∣ monsterOrder) :
    (p = 2 ∧ k ≤ 46) ∨ (p = 3 ∧ k ≤ 20) := by
  rcases prime_two_or_three_of_pow_ten_dvd hp hk h with rfl | rfl
  · exact Or.inl ⟨rfl, le_of_two_pow_dvd h⟩
  · exact Or.inr ⟨rfl, le_of_three_pow_dvd h⟩

theorem bounds_of_pow_dvd {f m : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m)
    (hb : f * (m * (m + 1) / 2) ≤ 46) : f ≤ 4 ∧ m ≤ 9 := by
  have he : 10 ≤ m * (m + 1) / 2 := by
    have : 20 ≤ m * (m + 1) := by nlinarith
    omega
  refine ⟨by nlinarith, ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : 110 ≤ m * (m + 1) := by nlinarith
  have h2 : 55 ≤ m * (m + 1) / 2 := by omega
  nlinarith

theorem ordA_five_false {p f m : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hm : 4 ≤ m) (h5m : 5 ∣ m + 1)
    (h5q : 5 ∣ p ^ f - 1) (hd : ordA m (p ^ f) ∣ monsterOrder) : False := by
  have hpow : p ^ (f * (m * (m + 1) / 2)) ∣ monsterOrder := by
    have := (pow_dvd_ordA (q := p ^ f) (n := m) (by omega)).trans hd
    rwa [← pow_mul] at this
  have he : 10 ≤ m * (m + 1) / 2 := by
    have : 20 ≤ m * (m + 1) := by nlinarith
    omega
  have hk : 10 ≤ f * (m * (m + 1) / 2) := le_trans he (Nat.le_mul_of_pos_left _ hf)
  rcases bound_of_pow_dvd hp hk hpow with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  all_goals
    obtain ⟨hf4, hm9⟩ := bounds_of_pow_dvd hf hm (by omega)
    interval_cases m <;> interval_cases f <;>
      first
        | omega
        | (exfalso; revert h5m; decide)
        | (exfalso; revert h5q; norm_num; done)
        | exact absurd hd (by decide +kernel)

theorem ordTwistedA_five {p f m : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hm : 4 ≤ m)
    (h5m : 5 ∣ m + 1) (h5q : 5 ∣ p ^ f + 1) (hd : ordTwistedA m (p ^ f) ∣ monsterOrder) :
    p = 2 ∧ f = 2 ∧ m = 4 := by
  have hpow : p ^ (f * (m * (m + 1) / 2)) ∣ monsterOrder := by
    have := (pow_dvd_ordTwistedA (q := p ^ f) (n := m) (by omega)).trans hd
    rwa [← pow_mul] at this
  have he : 10 ≤ m * (m + 1) / 2 := by
    have : 20 ≤ m * (m + 1) := by nlinarith
    omega
  have hk : 10 ≤ f * (m * (m + 1) / 2) := le_trans he (Nat.le_mul_of_pos_left _ hf)
  rcases bound_of_pow_dvd hp hk hpow with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  all_goals
    obtain ⟨hf4, hm9⟩ := bounds_of_pow_dvd hf hm (by omega)
    interval_cases m <;> interval_cases f <;>
      first
        | omega
        | (exfalso; revert h5m; decide)
        | (exfalso; revert h5q; norm_num; done)
        | exact absurd hd (by decide +kernel)

theorem thirteen_mul_fortyOne_dvd_ordTwistedA : 13 * 41 ∣ ordTwistedA 4 (2 ^ 2) := by
  decide +kernel

end CFSG.HardMathSupport.Dickson.I271.FiveCentralArith
