module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSporOrder

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem prime_dvd_suz {p : ℕ} (hp : p.Prime) (h : p ∣ 448345497600) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  rw [show (448345497600 : ℕ) = 2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13 by norm_num] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h13
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h11
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
        · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
          · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
          · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)))
        · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) (hp.dvd_of_dvd_pow h5))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) h7))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) h11)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 13 (by norm_num) h13)))))

theorem prime_dvd_onan {p : ℕ} (hp : p.Prime) (h : p ∣ 460815505920) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 31 := by
  rw [show (460815505920 : ℕ) = 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31 by norm_num] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h31
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h19
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h11
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
          · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
            · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
            · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)))
          · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) h5)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h7)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) h11)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 19 (by norm_num) h19))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 31 (by norm_num) h31))))))

theorem le_five_of_choose_le_thirteen {n : ℕ} (h : n * (n - 1) / 2 ≤ 13) : n ≤ 5 := by
  by_contra hn
  have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul (show 6 ≤ n by omega) (show 5 ≤ n - 1 by omega)
  omega

theorem le_three_of_sq_le_thirteen {n : ℕ} (h : n ^ 2 ≤ 13) : n ≤ 3 := by
  by_contra hn
  have : 4 * 4 ≤ n * n := Nat.mul_le_mul (show 4 ≤ n by omega) (show 4 ≤ n by omega)
  rw [sq] at h
  omega

theorem lie_casework13 {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hb : lieSylowExponent t n * f ≤ 13) :
    (t = .PSL ∨ t = .PSU) ∧ 2 ≤ n ∧ n ≤ 5 ∧ 1 ≤ f ∧ f ≤ 13 ∨
      (t = .PSp ∨ t = .POmegaOdd) ∧ 2 ≤ n ∧ n ≤ 3 ∧ 1 ≤ f ∧ f ≤ 13 ∨
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ n = 4 ∧ f = 1 ∨
      (t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧
        t ≠ .POmegaMinus) ∧ n = 0 ∧ 1 ≤ f ∧ f ≤ 6 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t <;> simp only [lieSylowExponent] at hb
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn2 (show 1 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inl rfl, hn2, le_five_of_choose_le_thirteen (by omega), hf, by omega⟩
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (show 2 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inr rfl, by omega, le_five_of_choose_le_thirteen (by omega), hf, by omega⟩
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inl rfl, hn2, le_three_of_sq_le_thirteen (by omega), hf, by omega⟩)
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inr rfl, by omega, le_three_of_sq_le_thirteen (by omega), hf,
      by omega⟩)
  · have hn4 : 4 ≤ n := hadm.2.2
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (show 3 ≤ n - 1 by omega)
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    have hn : n = 4 := by
      by_contra hne
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (show 5 ≤ n by omega) (show 4 ≤ n - 1 by omega)
      omega
    subst hn
    exact Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl, by omega⟩))
  · have hn4 : 4 ≤ n := hadm.2.2
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (show 3 ≤ n - 1 by omega)
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    have hn : n = 4 := by
      by_contra hne
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul (show 5 ≤ n by omega) (show 4 ≤ n - 1 by omega)
      omega
    subst hn
    exact Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩))

theorem lieModel_card_ne_suz (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 448345497600 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 448345497600 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 448345497600 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_suz hp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 13) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework13 hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem lieModel_card_ne_onan (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 460815505920 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 460815505920 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 460815505920 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_onan hp hpd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem factorial_div_two_ne_of_bounds {N : ℕ} (h1 : (14 : ℕ).factorial / 2 < N)
    (h2 : N < (15 : ℕ).factorial / 2) (k : ℕ) : k.factorial / 2 ≠ N := by
  intro hk
  rcases le_or_gt k 14 with hk14 | hk15
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le hk14)
    omega
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le (show 15 ≤ k by omega))
    omega

theorem not_dvd_card_carrier_suz
    {s : TauCeti.SporadicName} (hSuz : s ≠ .Suz) (hFi22 : s ≠ .Fi22) (hFi23 : s ≠ .Fi23)
    (hFi24Prime : s ≠ .Fi24Prime) (hCo1 : s ≠ .Co1) (hB : s ≠ .B) (hM : s ≠ .M) :
    ¬ 448345497600 ∣ Nat.card (NativeSporadic.Carrier s) := by
  cases s with
  | M11 => rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]; decide
  | M12 => rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]; decide
  | M22 => rw [show Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.M22 from rfl,
      Sporadic.Mathieu.card_M22]; decide
  | M23 => rw [show Nat.card (NativeSporadic.Carrier .M23) = Nat.card NativeSporadic.M23 from rfl,
      Sporadic.Schreier.m23_card]; decide
  | M24 => rw [show Nat.card (NativeSporadic.Carrier .M24) = Nat.card NativeSporadic.M24 from rfl,
      Sporadic.Mathieu.card_M24]; decide
  | J1 =>
    rcases SectionRank.card_small_sporadic (s := .J1) (Or.inr (Or.inr (Or.inr rfl))) with
      h | h | h | h <;> rw [h] <;> decide
  | J2 => rw [show Nat.card (NativeSporadic.Carrier .J2) = Nat.card NativeSporadic.J2 from rfl,
      Sporadic.J2.card_J2]; decide
  | J3 => rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]; decide
  | J4 => rw [show Nat.card (NativeSporadic.Carrier .J4) = Nat.card NativeSporadic.J4 from rfl,
      Sporadic.J4.card_J4]; decide
  | Co1 => exact absurd rfl hCo1
  | Co2 => rw [show Nat.card (NativeSporadic.Carrier .Co2) = Nat.card NativeSporadic.Co2 from rfl,
      Sporadic.Co2.card_Co2]; decide
  | Co3 => rw [show Nat.card (NativeSporadic.Carrier .Co3) = Nat.card NativeSporadic.Co3 from rfl,
      Sporadic.Co3.card_Co3]; decide
  | Fi22 => exact absurd rfl hFi22
  | Fi23 => exact absurd rfl hFi23
  | Fi24Prime => exact absurd rfl hFi24Prime
  | HS => rw [show Nat.card (NativeSporadic.Carrier .HS) = Nat.card NativeSporadic.HS from rfl,
      Sporadic.HS.card_HS]; decide
  | McL => rw [show Nat.card (NativeSporadic.Carrier .McL) = Nat.card NativeSporadic.McL from rfl,
      Sporadic.McL.card_McL]; decide
  | He => rw [show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl,
      Sporadic.He.card_He]; decide
  | Ru => rw [show Nat.card (NativeSporadic.Carrier .Ru) = Nat.card NativeSporadic.Ru from rfl,
      Sporadic.Ru.card_Ru]; decide
  | Suz => exact absurd rfl hSuz
  | ONan => rw [show Nat.card (NativeSporadic.Carrier .ONan) = Nat.card NativeSporadic.ON from rfl,
      Sporadic.ONOddCore.card_native_ON]; decide
  | HN => rw [show Nat.card (NativeSporadic.Carrier .HN) = Nat.card NativeSporadic.HN from rfl,
      Sporadic.HNSchreier.card_HN]; decide
  | Ly => rw [show Nat.card (NativeSporadic.Carrier .Ly) = Nat.card NativeSporadic.Ly from rfl,
      Sporadic.Ly.card_Ly]; decide
  | Th => rw [show Nat.card (NativeSporadic.Carrier .Th) = Nat.card NativeSporadic.Th from rfl,
      UnbalancedCorr.card_nativeTh]; decide
  | B => exact absurd rfl hB
  | M => exact absurd rfl hM

theorem not_dvd_card_carrier_onan
    {s : TauCeti.SporadicName} (hONan : s ≠ .ONan) (hM : s ≠ .M) :
    ¬ 460815505920 ∣ Nat.card (NativeSporadic.Carrier s) := by
  cases s with
  | M11 => rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]; decide
  | M12 => rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]; decide
  | M22 => rw [show Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.M22 from rfl,
      Sporadic.Mathieu.card_M22]; decide
  | M23 => rw [show Nat.card (NativeSporadic.Carrier .M23) = Nat.card NativeSporadic.M23 from rfl,
      Sporadic.Schreier.m23_card]; decide
  | M24 => rw [show Nat.card (NativeSporadic.Carrier .M24) = Nat.card NativeSporadic.M24 from rfl,
      Sporadic.Mathieu.card_M24]; decide
  | J1 =>
    rcases SectionRank.card_small_sporadic (s := .J1) (Or.inr (Or.inr (Or.inr rfl))) with
      h | h | h | h <;> rw [h] <;> decide
  | J2 => rw [show Nat.card (NativeSporadic.Carrier .J2) = Nat.card NativeSporadic.J2 from rfl,
      Sporadic.J2.card_J2]; decide
  | J3 => rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]; decide
  | J4 => rw [show Nat.card (NativeSporadic.Carrier .J4) = Nat.card NativeSporadic.J4 from rfl,
      Sporadic.J4.card_J4]; decide
  | Co1 => rw [show Nat.card (NativeSporadic.Carrier .Co1) = Nat.card NativeSporadic.Co1 from rfl,
      Sporadic.Co1.card_Co1]; decide
  | Co2 => rw [show Nat.card (NativeSporadic.Carrier .Co2) = Nat.card NativeSporadic.Co2 from rfl,
      Sporadic.Co2.card_Co2]; decide
  | Co3 => rw [show Nat.card (NativeSporadic.Carrier .Co3) = Nat.card NativeSporadic.Co3 from rfl,
      Sporadic.Co3.card_Co3]; decide
  | Fi22 =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi22) = Nat.card NativeSporadic.Fi22 from rfl,
      Sporadic.Fi22.card_Fi22]; decide
  | Fi23 =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi23) = Nat.card NativeSporadic.Fi23 from rfl,
      Sporadic.Fi23.card_Fi23]; decide
  | Fi24Prime =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi24Prime) = Nat.card NativeSporadic.Fi24prime
      from rfl, Sporadic.Fi24.card_Fi24prime]; decide
  | HS => rw [show Nat.card (NativeSporadic.Carrier .HS) = Nat.card NativeSporadic.HS from rfl,
      Sporadic.HS.card_HS]; decide
  | McL => rw [show Nat.card (NativeSporadic.Carrier .McL) = Nat.card NativeSporadic.McL from rfl,
      Sporadic.McL.card_McL]; decide
  | He => rw [show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl,
      Sporadic.He.card_He]; decide
  | Ru => rw [show Nat.card (NativeSporadic.Carrier .Ru) = Nat.card NativeSporadic.Ru from rfl,
      Sporadic.Ru.card_Ru]; decide
  | Suz => rw [show Nat.card (NativeSporadic.Carrier .Suz) = Nat.card NativeSporadic.Suz from rfl,
      Sporadic.Suz.card_Suz]; decide
  | ONan => exact absurd rfl hONan
  | HN => rw [show Nat.card (NativeSporadic.Carrier .HN) = Nat.card NativeSporadic.HN from rfl,
      Sporadic.HNSchreier.card_HN]; decide
  | Ly => rw [show Nat.card (NativeSporadic.Carrier .Ly) = Nat.card NativeSporadic.Ly from rfl,
      Sporadic.Ly.card_Ly]; decide
  | Th => rw [show Nat.card (NativeSporadic.Carrier .Th) = Nat.card NativeSporadic.Th from rfl,
      UnbalancedCorr.card_nativeTh]; decide
  | B => rw [show Nat.card (NativeSporadic.Carrier .B) = Nat.card NativeSporadic.B from rfl,
      card_nativeB']; decide
  | M => exact absurd rfl hM

end CFSG.ComponentClassification.GrSLit.L34Sec5S
