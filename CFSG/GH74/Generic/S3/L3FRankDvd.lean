module

public import CFSG.GH74.Generic.S3.L3ClassC2T2

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordRee)

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    refine ⟨m + 2, ?_⟩
    rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    refine ⟨m, ?_⟩
    rw [show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp [mul_comm]

theorem pow_dvd_ordA {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) : q ^ (m * (m + 1) / 2) ∣ ordA m q := by
  have hg : Nat.gcd (m + 1) (q - 1) ∣
      q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans ?_)
    exact Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hmul : ordA m q * Nat.gcd (m + 1) (q - 1) =
      q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - 1) := by
    unfold ordA
    exact Nat.div_mul_cancel hg
  have hcop : Nat.Coprime (q ^ (m * (m + 1) / 2)) (Nat.gcd (m + 1) (q - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) ?_
    obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
    simp
  have : q ^ (m * (m + 1) / 2) ∣ ordA m q * Nat.gcd (m + 1) (q - 1) := by
    rw [hmul]; exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right this

theorem toNat_sq (q : ℕ) : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [this]; exact Int.toNat_natCast _

theorem pow_dvd_ordTwistedA {m q : ℕ} (hm : 1 ≤ m) : q ^ (m * (m + 1) / 2) ∣ ordTwistedA m q := by
  have hg : Nat.gcd (m + 1) (q + 1) ∣
      q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - (-1 : ℤ) ^ i).toNat := by
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 : q + 1 ∣ (q ^ 2 - (-1 : ℤ) ^ 2).toNat := by
      rw [toNat_sq]; exact add_one_dvd_sq_sub_one q
    exact h2.trans (Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))
  have hmul : ordTwistedA m q * Nat.gcd (m + 1) (q + 1) =
      q ^ (m * (m + 1) / 2) * ∏ i ∈ Finset.Icc 2 (m + 1), (q ^ i - (-1 : ℤ) ^ i).toNat := by
    unfold ordTwistedA
    exact Nat.div_mul_cancel hg
  have hcop : Nat.Coprime (q ^ (m * (m + 1) / 2)) (Nat.gcd (m + 1) (q + 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) ?_
    simp
  have : q ^ (m * (m + 1) / 2) ∣ ordTwistedA m q * Nat.gcd (m + 1) (q + 1) := by
    rw [hmul]; exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right this

theorem pow_dvd_ordBC {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) : q ^ (m * m) ∣ ordBC m q := by
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ (m * m) * ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans ?_)
    exact Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  have hmul : ordBC m q * Nat.gcd 2 (q - 1) =
      q ^ (m * m) * ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) := by
    unfold ordBC
    exact Nat.div_mul_cancel hg
  have hcop : Nat.Coprime (q ^ (m * m)) (Nat.gcd 2 (q - 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) ?_
    obtain ⟨a, rfl⟩ : ∃ a, q = a + 1 := ⟨q - 1, by omega⟩
    simp
  have : q ^ (m * m) ∣ ordBC m q * Nat.gcd 2 (q - 1) := by
    rw [hmul]; exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right this

theorem pow_dvd_ordG2 (q : ℕ) : q ^ 6 ∣ ordG2 q :=
  ⟨(q ^ 6 - 1) * (q ^ 2 - 1), by unfold ordG2; ring⟩

theorem pow_dvd_ordTrialityD4 (q : ℕ) : q ^ 12 ∣ ordTrialityD4 q :=
  ⟨(q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1), by unfold ordTrialityD4; ring⟩

theorem pow_dvd_ordRee (q : ℕ) : q ^ 3 ∣ ordRee q :=
  ⟨(q ^ 3 + 1) * (q - 1), by unfold ordRee; ring⟩


theorem three_mul_ge {q N : ℕ} (hq : 1 ≤ q) (hN : N = ordA 2 q ∨ N = ordTwistedA 2 q) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N := by
  rcases hN with rfl | rfl
  · have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h := ordA_two_mul q hq
    calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = ordA 2 q * Nat.gcd 3 (q - 1) := h.symm
      _ ≤ ordA 2 q * 3 := Nat.mul_le_mul_left _ hg
      _ = 3 * ordA 2 q := mul_comm _ _
  · have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h := ordTwistedA_two_mul q
    calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = ordTwistedA 2 q * Nat.gcd 3 (q + 1) := h.symm
      _ ≤ ordTwistedA 2 q * 3 := Nat.mul_le_mul_left _ hg
      _ = 3 * ordTwistedA 2 q := mul_comm _ _

theorem le_of_ord {q N : ℕ} (hq : 5 ≤ q) (hN : N = ordA 2 q ∨ N = ordTwistedA 2 q) :
    124000 ≤ N := by
  rcases hN with rfl | rfl
  · exact le_ordA_two hq
  · exact le_ordTwistedA_two hq

theorem fb_A1 {q q' : ℕ} (hq : 1 ≤ q) (h : q' ≤ q ^ 3) : q' * 6 ≤ q ^ 4 * 6 := by
  have : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  omega

theorem fb_A2 {q q' : ℕ} (h : q' ^ 3 ≤ q ^ 3) : q' ^ 4 * 6 ≤ q ^ 4 * 6 := by
  have h1 : q' ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).1 h
  have := Nat.pow_le_pow_left h1 4
  omega

theorem fb_C2 {q q' : ℕ} (hq : 5 ≤ q) (h : q' ^ 4 ≤ q ^ 3) : q' ^ 4 * 6 + 3 ≤ q ^ 4 * 6 := by
  have h1 : q ^ 4 = q * q ^ 3 := by ring
  have h2 : 5 * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem fb_G2 {q q' : ℕ} (hq : 5 ≤ q) (h : q' ^ 6 ≤ q ^ 3) : q' ^ 4 * 6 + 5 ≤ q ^ 4 * 6 := by
  have h1 : (q' ^ 2) ^ 3 ≤ q ^ 3 := by rw [← pow_mul]; exact h
  have h2 : q' ^ 2 ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).1 h1
  have h3 : q' ^ 4 ≤ q ^ 2 := by
    calc q' ^ 4 = (q' ^ 2) ^ 2 := by ring
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
  have h5 : 25 * q ^ 2 ≤ q ^ 2 * q ^ 2 := by
    have : 5 * 5 ≤ q * q := Nat.mul_le_mul hq hq
    nlinarith [Nat.zero_le (q ^ 2)]
  have h6 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end CFSG.GH74.Generic.S3.L3Ord
