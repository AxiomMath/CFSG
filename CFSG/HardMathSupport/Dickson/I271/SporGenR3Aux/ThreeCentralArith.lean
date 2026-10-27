module

public import CFSG.Open.OrderForm
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralArith

public section

namespace CFSG.HardMathSupport.Dickson.I271.ThreeCentralArith

open CFSG.Open CFSG.HardMathSupport.Dickson.I271.FiveCentralArith

theorem prime_pow_dvd_monsterOrder {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k)
    (h : p ^ k ∣ monsterOrder) : (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13) ∧ k ≤ 46 := by
  have hpM : p ∣ monsterOrder := (dvd_pow_self p (by omega)).trans h
  have h3 : p ^ 3 ∣ monsterOrder := (pow_dvd_pow p hk).trans h
  refine ⟨?_, ?_⟩
  · rcases prime_dvd_monsterOrder hp hpM with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (simp; done)
      | (exfalso; unfold monsterOrder at h3; norm_num at h3)
  · by_contra hc
    have h47 : p ^ 47 ∣ monsterOrder := (pow_dvd_pow p (by omega)).trans h
    rcases prime_dvd_monsterOrder hp hpM with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (unfold monsterOrder at h47; norm_num at h47)

theorem ordA_three_false {p f m : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hm : 2 ≤ m) (h3m : 3 ∣ m + 1)
    (h3q : 3 ∣ p ^ f - 1) (hd : ordA m (p ^ f) ∣ monsterOrder)
    (h12 : 3 ^ 12 ∣ ordA m (p ^ f)) : False := by
  have hpow : p ^ (f * (m * (m + 1) / 2)) ∣ monsterOrder := by
    have := (pow_dvd_ordA (q := p ^ f) (n := m) (by omega)).trans hd
    rwa [← pow_mul] at this
  have he : 3 ≤ m * (m + 1) / 2 := by
    have : 6 ≤ m * (m + 1) := by nlinarith
    omega
  have hk : 3 ≤ f * (m * (m + 1) / 2) := le_trans he (Nat.le_mul_of_pos_left _ hf)
  obtain ⟨hpl, hk46⟩ := prime_pow_dvd_monsterOrder hp hk hpow
  have hf46 : f ≤ 46 := le_trans (Nat.le_mul_of_pos_right f (by omega)) hk46
  have hm9 : m ≤ 9 := by
    by_contra hc
    push Not at hc
    have h1 : 110 ≤ m * (m + 1) := by nlinarith
    have h2 : 55 ≤ m * (m + 1) / 2 := by omega
    have h3 : m * (m + 1) / 2 ≤ f * (m * (m + 1) / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  have key : ∀ p ∈ ([2, 3, 5, 7, 13] : List ℕ), ∀ m ∈ List.range 10, ∀ f ∈ List.range 47,
      2 ≤ m → 1 ≤ f → 3 ∣ m + 1 → 3 ∣ p ^ f - 1 → ordA m (p ^ f) ∣ monsterOrder →
        3 ^ 12 ∣ ordA m (p ^ f) → False := by
    decide +kernel
  exact key p (by rcases hpl with rfl | rfl | rfl | rfl | rfl <;> simp) m
    (List.mem_range.2 (by omega)) f (List.mem_range.2 (by omega)) hm hf h3m h3q hd h12

theorem ordTwistedA_three_false {p f m : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hm : 2 ≤ m)
    (h3m : 3 ∣ m + 1) (h3q : 3 ∣ p ^ f + 1) (hd : ordTwistedA m (p ^ f) ∣ monsterOrder)
    (h12 : 3 ^ 12 ∣ ordTwistedA m (p ^ f)) : False := by
  have hpow : p ^ (f * (m * (m + 1) / 2)) ∣ monsterOrder := by
    have := (pow_dvd_ordTwistedA (q := p ^ f) (n := m) (by omega)).trans hd
    rwa [← pow_mul] at this
  have he : 3 ≤ m * (m + 1) / 2 := by
    have : 6 ≤ m * (m + 1) := by nlinarith
    omega
  have hk : 3 ≤ f * (m * (m + 1) / 2) := le_trans he (Nat.le_mul_of_pos_left _ hf)
  obtain ⟨hpl, hk46⟩ := prime_pow_dvd_monsterOrder hp hk hpow
  have hf46 : f ≤ 46 := le_trans (Nat.le_mul_of_pos_right f (by omega)) hk46
  have hm9 : m ≤ 9 := by
    by_contra hc
    push Not at hc
    have h1 : 110 ≤ m * (m + 1) := by nlinarith
    have h2 : 55 ≤ m * (m + 1) / 2 := by omega
    have h3 : m * (m + 1) / 2 ≤ f * (m * (m + 1) / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  have key : ∀ p ∈ ([2, 3, 5, 7, 13] : List ℕ), ∀ m ∈ List.range 10, ∀ f ∈ List.range 47,
      2 ≤ m → 1 ≤ f → 3 ∣ m + 1 → 3 ∣ p ^ f + 1 → ordTwistedA m (p ^ f) ∣ monsterOrder →
        3 ^ 12 ∣ ordTwistedA m (p ^ f) → False := by
    decide +kernel
  exact key p (by rcases hpl with rfl | rfl | rfl | rfl | rfl <;> simp) m
    (List.mem_range.2 (by omega)) f (List.mem_range.2 (by omega)) hm hf h3m h3q hd h12

theorem coprime_sub_one {q : ℕ} (hq : 1 ≤ q) : Nat.Coprime q (q - 1) := by
  have h : Nat.Coprime (q - 1) ((q - 1) + 1) := by simp
  rw [Nat.sub_add_cancel hq] at h
  exact h.symm

theorem add_one_dvd_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  refine ⟨r, ?_⟩
  have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  omega

theorem pow_dvd_orderE6 {q : ℕ} (hq : 2 ≤ q) : q ^ 36 ∣ orderE6 q := by
  have hg : Nat.gcd 3 (q - 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one q 2)) _
  have hcop : Nat.Coprime (q ^ 36) (Nat.gcd 3 (q - 1)) :=
    Nat.Coprime.pow_left 36
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (coprime_sub_one (by omega)))
  have hdiv : q ^ 36 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) :=
    ((((((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)
  unfold orderE6
  have h1 := Nat.div_mul_cancel hg
  rw [← h1] at hdiv
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem pow_dvd_orderTwistedE6 {q : ℕ} (hq : 2 ≤ q) : q ^ 36 ∣ orderTwistedE6 q := by
  have hg : Nat.gcd 3 (q + 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (add_one_dvd_sq_sub_one (by omega))) _
  have hcop : Nat.Coprime (q ^ 36) (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.pow_left 36
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (by simp))
  have hdiv : q ^ 36 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) :=
    ((((((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)
  unfold orderTwistedE6
  have h1 := Nat.div_mul_cancel hg
  rw [← h1] at hdiv
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem prime_of_pow_36_dvd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : (p ^ f) ^ 36 ∣ monsterOrder) : (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13) ∧ f = 1 := by
  rw [← pow_mul] at h
  obtain ⟨hpl, hk⟩ := prime_pow_dvd_monsterOrder hp (by omega) h
  exact ⟨hpl, by omega⟩

theorem orderE6_three_false {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h3q : 3 ∣ p ^ f - 1)
    (hd : orderE6 (p ^ f) ∣ monsterOrder) : False := by
  have hq2 : 2 ≤ p ^ f :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.pos hf)
  obtain ⟨hpl, rfl⟩ := prime_of_pow_36_dvd hp hf ((pow_dvd_orderE6 hq2).trans hd)
  rw [pow_one] at h3q hd
  have key : ∀ p ∈ ([2, 3, 5, 7, 13] : List ℕ), 3 ∣ p - 1 → orderE6 p ∣ monsterOrder → False := by
    decide +kernel
  exact key p (by rcases hpl with rfl | rfl | rfl | rfl | rfl <;> simp) h3q hd

theorem orderTwistedE6_three_false {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h3q : 3 ∣ p ^ f + 1)
    (hd : orderTwistedE6 (p ^ f) ∣ monsterOrder) (h12 : 3 ^ 12 ∣ orderTwistedE6 (p ^ f)) :
    False := by
  have hq2 : 2 ≤ p ^ f :=
    hp.two_le.trans (by simpa using Nat.pow_le_pow_right hp.pos hf)
  obtain ⟨hpl, rfl⟩ := prime_of_pow_36_dvd hp hf ((pow_dvd_orderTwistedE6 hq2).trans hd)
  rw [pow_one] at h3q hd h12
  have key : ∀ p ∈ ([2, 3, 5, 7, 13] : List ℕ), 3 ∣ p + 1 → orderTwistedE6 p ∣ monsterOrder →
      3 ^ 12 ∣ orderTwistedE6 p → False := by
    decide +kernel
  exact key p (by rcases hpl with rfl | rfl | rfl | rfl | rfl <;> simp) h3q hd h12

theorem not_pow_dvd_ordA_one_nine : ¬ 3 ^ 12 ∣ ordA 1 (3 ^ 2) := by decide +kernel

theorem not_pow_dvd_ordTwistedA_three_three : ¬ 3 ^ 12 ∣ ordTwistedA 3 (3 ^ 1) := by
  decide +kernel

theorem not_pow_dvd_ordBC_three_three : ¬ 3 ^ 12 ∣ ordBC 3 (3 ^ 1) := by decide +kernel

theorem not_pow_dvd_orderG2_three : ¬ 3 ^ 12 ∣ orderG2 (3 ^ 1) := by decide +kernel

end CFSG.HardMathSupport.Dickson.I271.ThreeCentralArith
