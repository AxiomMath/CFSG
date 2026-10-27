module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open

theorem succ_dvd_toNat_pow_sub {q i : ℕ} (hq : 1 ≤ q) (hi : 1 ≤ i) :
    q + 1 ∣ (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) := by
  have hpos : (0 : ℤ) ≤ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
    have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq)
    have h2 : (-1 : ℤ) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
    by_cases hq1 : q = 1
    · subst hq1
      rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
    · have h3 : (2 : ℤ) ≤ q := by omega
      have h4 : (2 : ℤ) ≤ (q : ℤ) ^ i := by
        calc (2 : ℤ) ≤ q := h3
          _ = (q : ℤ) ^ 1 := (pow_one _).symm
          _ ≤ (q : ℤ) ^ i := pow_le_pow_right₀ (by omega) hi
      linarith
  have hdvd : ((q + 1 : ℕ) : ℤ) ∣ (q : ℤ) ^ i - (-1 : ℤ) ^ i := by
    have := sub_dvd_pow_sub_pow (q : ℤ) (-1) i
    simpa [sub_neg_eq_add] using this
  have h2 : ((q + 1 : ℕ) : ℤ) ∣ (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat : ℤ) := by
    rwa [Int.toNat_of_nonneg hpos]
  exact_mod_cast h2

theorem toNat_pow_sub_two (q : ℕ) :
    (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  · have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [this]
      ring
    rw [h, Int.toNat_natCast]

theorem three_dvd_ordTwistedA {f m : ℕ} (hf : 1 ≤ f) (hm : 2 ≤ m) :
    3 ∣ ordTwistedA (m - 1) (2 ^ f) := by
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h3q : 3 ∣ q ^ 2 - 1 := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
    simpa using this
  have h2mem : 2 ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨le_rfl, hm⟩
  unfold ordTwistedA
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  set T : ℕ → ℕ := fun i => (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) with hT
  set e := (m - 1) * m / 2 with he
  set Num := q ^ e * ∏ i ∈ Finset.Icc 2 m, T i with hNum
  set g := Nat.gcd m (q + 1) with hg
  have hgq : g ∣ q + 1 := Nat.gcd_dvd_right _ _
  have hgm : g ∣ m := Nat.gcd_dvd_left _ _
  have hT2 : T 2 = q ^ 2 - 1 := toNat_pow_sub_two q
  have hprod2 : T 2 ∣ ∏ i ∈ Finset.Icc 2 m, T i := Finset.dvd_prod_of_mem T h2mem
  have hgNum : g ∣ Num := by
    refine Dvd.dvd.mul_left ?_ _
    refine hgq.trans (Dvd.dvd.trans ?_ hprod2)
    exact succ_dvd_toNat_pow_sub (i := 2) hq1 (by omega)
  have hmul : Num / g * g = Num := Nat.div_mul_cancel hgNum
  by_cases h3g : 3 ∣ g
  ·
    have h3q1 : 3 ∣ q + 1 := h3g.trans hgq
    have h3m : 3 ∣ m := h3g.trans hgm
    have hm3 : 3 ≤ m := by
      obtain ⟨c, hc⟩ := h3m
      omega
    have h3mem : 3 ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨by omega, hm3⟩
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 m := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption
    have hpair : T 2 * T 3 ∣ ∏ i ∈ Finset.Icc 2 m, T i := by
      have := Finset.prod_dvd_prod_of_subset _ _ T hsub
      rwa [Finset.prod_pair (by norm_num)] at this
    have hsq : (q + 1) * (q + 1) ∣ ∏ i ∈ Finset.Icc 2 m, T i :=
      (mul_dvd_mul (succ_dvd_toNat_pow_sub hq1 (by omega))
        (succ_dvd_toNat_pow_sub hq1 (by omega))).trans hpair
    obtain ⟨C, hC⟩ := hsq
    obtain ⟨u, hu⟩ := hgq
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hNum' : Num = g * (q ^ e * u * (g * u) * C) := by
      rw [hNum, hC, hu]
      ring
    have hN : Num / g = q ^ e * u * (g * u) * C := by
      rw [hNum', Nat.mul_div_cancel_left _ hgpos]
    have hN2 : (q + 1) ∣ Num / g := by
      rw [hN]
      exact ⟨q ^ e * u * C, by rw [hu]; ring⟩
    exact h3q1.trans hN2
  · have h3Num : 3 ∣ Num := by
      refine Dvd.dvd.mul_left ?_ _
      exact (hT2 ▸ h3q).trans hprod2
    rw [← hmul] at h3Num
    exact ((Nat.Prime.dvd_mul Nat.prime_three).1 h3Num).resolve_right h3g

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
