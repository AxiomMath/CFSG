module

public import CFSG.Open.StatedDefs
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux

open CFSG.Open

theorem toNat_pow_sub {q : ℕ} {ε : ℤ} (hq : 1 ≤ q) (hε : ε = 1 ∨ ε = -1) (i : ℕ) :
    (((q : ℤ) ^ i - ε ^ i).toNat : ℤ) = (q : ℤ) ^ i - ε ^ i := by
  apply Int.toNat_of_nonneg
  have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq)
  rcases hε with rfl | rfl
  · rw [one_pow]; linarith
  · rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith

theorem five_dvd_toNat_pow_sub {q : ℕ} {ε : ℤ} (hq : 1 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (h5 : (5 : ℤ) ∣ (q : ℤ) - ε) (i : ℕ) : 5 ∣ ((q : ℤ) ^ i - ε ^ i).toNat := by
  have h1 : (5 : ℤ) ∣ (q : ℤ) ^ i - ε ^ i := h5.trans (sub_dvd_pow_sub_pow _ _ _)
  rw [← toNat_pow_sub hq hε i] at h1
  exact_mod_cast h1

theorem twentyfive_dvd_toNat_pow_sub {q : ℕ} {ε : ℤ} (hq : 1 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (h25 : (25 : ℤ) ∣ (q : ℤ) - ε) (i : ℕ) : 25 ∣ ((q : ℤ) ^ i - ε ^ i).toNat := by
  have h1 : (25 : ℤ) ∣ (q : ℤ) ^ i - ε ^ i := h25.trans (sub_dvd_pow_sub_pow _ _ _)
  rw [← toNat_pow_sub hq hε i] at h1
  exact_mod_cast h1

theorem twentyfive_dvd_toNat_pow_five {q : ℕ} {ε : ℤ} (hq : 1 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (h5 : (5 : ℤ) ∣ (q : ℤ) - ε) : 25 ∣ ((q : ℤ) ^ 5 - ε ^ 5).toNat := by
  obtain ⟨k, hk⟩ := h5
  have hq' : (q : ℤ) = ε + 5 * k := by linarith
  have h1 : (25 : ℤ) ∣ (q : ℤ) ^ 5 - ε ^ 5 := by
    rw [hq']
    exact ⟨ε ^ 4 * k + 10 * ε ^ 3 * k ^ 2 + 50 * ε ^ 2 * k ^ 3 + 125 * ε * k ^ 4 + 125 * k ^ 5,
      by ring⟩
  rw [← toNat_pow_sub hq hε 5] at h1
  exact_mod_cast h1

theorem five_pow_dvd_of_formula {q n D e c : ℕ} {ε : ℤ} (hq : 1 ≤ q) (hε : ε = 1 ∨ ε = -1)
    (hD : (D : ℤ) = (q : ℤ) - ε) (h5D : 5 ∣ D) (hn5 : 5 ∣ n) (hn : 2 ≤ n)
    (hc : c = (q ^ e * ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - ε ^ i).toNat) / Nat.gcd n D) :
    5 ^ 4 ∣ c ∧ (n ≠ 5 → 5 ^ 6 ∣ c) ∧ (25 ∣ D → 5 ^ 6 ∣ c) := by
  have h5 : (5 : ℤ) ∣ (q : ℤ) - ε := by rw [← hD]; exact_mod_cast h5D
  set T : ℕ → ℕ := fun i => ((q : ℤ) ^ i - ε ^ i).toNat with hT
  have hT5 : ∀ i, 5 ∣ T i := fun i => five_dvd_toNat_pow_sub hq hε h5 i
  have hTD : ∀ i, D ∣ T i := by
    intro i
    have h1 : (D : ℤ) ∣ (q : ℤ) ^ i - ε ^ i := by rw [hD]; exact sub_dvd_pow_sub_pow _ _ _
    have h2 : (D : ℤ) ∣ ((T i : ℕ) : ℤ) := by
      rw [hT]
      dsimp only
      rw [toNat_pow_sub hq hε i]
      exact h1
    exact_mod_cast h2
  rcases eq_or_ne n 5 with rfl | hn5'
  ·
    have hprod : ∏ i ∈ Finset.Icc 2 5, T i = T 2 * T 3 * T 4 * T 5 := by
      rw [show Finset.Icc 2 5 = {2, 3, 4, 5} from by decide]
      simp [Finset.prod_insert, mul_assoc]
    have hg : Nat.gcd 5 D = 5 := Nat.gcd_eq_left h5D
    have hM : 5 ∣ q ^ e * ∏ i ∈ Finset.Icc 2 5, T i := by
      rw [hprod]
      exact Dvd.dvd.mul_left
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hT5 2) _) _) _) _
    have hcM : c * 5 = q ^ e * ∏ i ∈ Finset.Icc 2 5, T i := by
      rw [hc, hg]
      exact Nat.div_mul_cancel hM
    refine ⟨?_, fun h => absurd rfl h, ?_⟩
    · have h25 : 25 ∣ T 5 := twentyfive_dvd_toNat_pow_five hq hε h5
      have h1 : 5 ^ 5 ∣ q ^ e * ∏ i ∈ Finset.Icc 2 5, T i := by
        rw [hprod]
        have : 5 ^ 5 ∣ T 2 * T 3 * T 4 * T 5 := by
          have := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (hT5 2) (hT5 3)) (hT5 4)) h25
          simpa using this
        exact Dvd.dvd.mul_left this _
      rw [← hcM] at h1
      have : 5 * 5 ^ 4 ∣ 5 * c := by
        rw [← pow_succ']
        simpa [mul_comm] using h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    · intro h25
      have h25' : (25 : ℤ) ∣ (q : ℤ) - ε := by rw [← hD]; exact_mod_cast h25
      have hTa : ∀ i, 25 ∣ T i := fun i => twentyfive_dvd_toNat_pow_sub hq hε h25' i
      have h1 : 5 ^ 7 ∣ q ^ e * ∏ i ∈ Finset.Icc 2 5, T i := by
        rw [hprod]
        have : 5 ^ 7 ∣ T 2 * T 3 * T 4 * T 5 := by
          have h2 := mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (hTa 2) (hTa 3)) (hTa 4)) (hT5 5)
          have : (25 * 25 * 25 * 5 : ℕ) = 5 ^ 7 := by norm_num
          rwa [this] at h2
        exact Dvd.dvd.mul_left this _
      rw [← hcM] at h1
      have : 5 * 5 ^ 6 ∣ 5 * c := by
        rw [← pow_succ']
        simpa [mul_comm] using h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  ·
    have hn10 : 10 ≤ n := by
      obtain ⟨k, rfl⟩ := hn5
      omega
    have hsplit : Finset.Icc 2 n = insert 2 (Finset.Icc 3 n) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2n : (2 : ℕ) ∉ Finset.Icc 3 n := by simp
    set P : ℕ := ∏ i ∈ Finset.Icc 3 n, T i with hP
    have hgD : Nat.gcd n D ∣ T 2 := (Nat.gcd_dvd_right n D).trans (hTD 2)
    obtain ⟨u, hu⟩ := hgD
    have hg0 : 0 < Nat.gcd n D := Nat.gcd_pos_of_pos_left _ (by omega)
    have hc' : c = q ^ e * u * P := by
      rw [hc, hsplit, Finset.prod_insert h2n, ← hP]
      change q ^ e * (T 2 * P) / Nat.gcd n D = _
      rw [hu]
      rw [show q ^ e * (Nat.gcd n D * u * P) = Nat.gcd n D * (q ^ e * u * P) by ring]
      exact Nat.mul_div_cancel_left _ hg0
    have hPd : 5 ^ 6 ∣ P := by
      have h1 : ∏ _i ∈ Finset.Icc 3 n, 5 ∣ P :=
        Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hT5 i)
      rw [Finset.prod_const, Nat.card_Icc] at h1
      exact (pow_dvd_pow 5 (by omega)).trans h1
    have h6 : 5 ^ 6 ∣ c := by
      rw [hc']
      exact Dvd.dvd.mul_left hPd _
    exact ⟨(pow_dvd_pow 5 (by norm_num)).trans h6, fun _ => h6, fun _ => h6⟩

theorem toNat_pow_sub_one_eq {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    ((q : ℤ) ^ i - 1 ^ i).toNat = q ^ i - 1 := by
  apply Nat.cast_injective (R := ℤ)
  rw [toNat_pow_sub hq (Or.inl rfl) i, Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rw [one_pow]

theorem five_pow_dvd_card_psl {K : Type} [Group K] {n ℓ f : ℕ}
    (h : StatedClassicalModel K .PSL n ℓ f) (hn5 : 5 ∣ n) (hq5 : 5 ∣ ℓ ^ f - 1) :
    5 ^ 4 ∣ Nat.card K ∧ (n ≠ 5 → 5 ^ 6 ∣ Nat.card K) ∧
      (25 ∣ ℓ ^ f - 1 → 5 ^ 6 ∣ Nat.card K) := by
  obtain ⟨hp, hf, hn2, -⟩ := h.1
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hp.pos
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by omega) h
  refine five_pow_dvd_of_formula (q := ℓ ^ f) (D := ℓ ^ f - 1) (e := n * (n - 1) / 2) (ε := 1) hq
    (Or.inl rfl) (by rw [Nat.cast_sub hq]; push_cast; ring) hq5 hn5 hn2 ?_
  have hprod : ∏ i ∈ Finset.Icc 2 n, ((ℓ ^ f) ^ i - 1) =
      ∏ i ∈ Finset.Icc 2 n, ((((ℓ ^ f : ℕ) : ℤ)) ^ i - 1 ^ i).toNat :=
    Finset.prod_congr rfl fun i _ => (toNat_pow_sub_one_eq hq i).symm
  rw [hcard, hprod]

theorem five_pow_dvd_card_psu {K : Type} [Group K] {n ℓ f : ℕ}
    (h : StatedClassicalModel K .PSU n ℓ f) (hn5 : 5 ∣ n) (hq5 : 5 ∣ ℓ ^ f + 1) :
    5 ^ 4 ∣ Nat.card K ∧ (n ≠ 5 → 5 ^ 6 ∣ Nat.card K) ∧
      (25 ∣ ℓ ^ f + 1 → 5 ^ 6 ∣ Nat.card K) := by
  obtain ⟨hp, hf, hn3, -⟩ := h.1
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hp.pos
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (by omega) h
  exact five_pow_dvd_of_formula (q := ℓ ^ f) (D := ℓ ^ f + 1) (e := n * (n - 1) / 2) (ε := -1) hq
    (Or.inr rfl) (by push_cast; ring) hq5 hn5 (by omega) hcard

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagAux
