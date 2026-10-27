module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG CFSG.Assembly.LowTwoRank

theorem lieSylowExponent_pos {t : StatedLieTag} {n p f : ℕ} (h : StatedLieAdmissible t n p f) :
    1 ≤ lieSylowExponent t n := by
  cases t <;> simp only [lieSylowExponent]
  · have hn : 2 ≤ n := h.2.2.1
    have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn (show 1 ≤ n - 1 by omega)
    omega
  · have hn : 3 ≤ n := h.2.2.1
    have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (show 2 ≤ n by omega) (show 1 ≤ n - 1 by omega)
    omega
  · have hn : 2 ≤ n := h.2.2.1
    exact Nat.one_le_pow _ _ (by omega)
  · have hn : 3 ≤ n := h.2.2.1
    exact Nat.one_le_pow _ _ (by omega)
  · have hn : 4 ≤ n := h.2.2
    have : 1 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ n - 1 by omega)
    omega
  · have hn : 4 ≤ n := h.2.2
    have : 1 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ n - 1 by omega)
    omega
  all_goals norm_num

theorem le_of_pow_dvd_of_not_dvd {p k v N : ℕ} (h : p ^ k ∣ N) (hN : ¬ p ^ (v + 1) ∣ N) :
    k ≤ v := by
  by_contra hk
  exact hN ((pow_dvd_pow p (by omega)).trans h)

theorem prime_dvd_held {p : ℕ} (hp : p.Prime) (h : p ∣ 4030387200) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
  rw [show (4030387200 : ℕ) = 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h17
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
      · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
            (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
          (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      h17))))

theorem prime_dvd_L34 {p : ℕ} (hp : p.Prime) (h : p ∣ 20160) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rw [show (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)))

theorem le_five_of_choose_le {n : ℕ} (h : n * (n - 1) / 2 ≤ 10) : n ≤ 5 := by
  by_contra hn
  have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul (show 6 ≤ n by omega) (show 5 ≤ n - 1 by omega)
  omega

theorem le_three_of_sq_le {n : ℕ} (h : n ^ 2 ≤ 10) : n ≤ 3 := by
  by_contra hn
  have : 4 * 4 ≤ n * n := Nat.mul_le_mul (show 4 ≤ n by omega) (show 4 ≤ n by omega)
  rw [sq] at h
  omega

theorem lie_bounds {X : Type} [Group X] (hO : LieOrderFormulasInput) {t : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : Blueprint.LieModel X t n p f)
    {v : ℕ} (hN : ¬ p ^ (v + 1) ∣ Nat.card X) :
    lieSylowExponent t n * f ≤ v ∧
      Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
  obtain ⟨-, hord, hfac⟩ := hO X t n p f hadm hX
  refine ⟨le_of_pow_dvd_of_not_dvd (hfac ▸ Nat.ordProj_dvd _ _) hN, hord⟩

theorem lie_casework {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hb : lieSylowExponent t n * f ≤ 10) :
    (t = .PSL ∨ t = .PSU) ∧ 2 ≤ n ∧ n ≤ 5 ∧ 1 ≤ f ∧ f ≤ 10 ∨
      (t = .PSp ∨ t = .POmegaOdd) ∧ 2 ≤ n ∧ n ≤ 3 ∧ 1 ≤ f ∧ f ≤ 10 ∨
      (t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧
        t ≠ .POmegaMinus) ∧ n = 0 ∧ 1 ≤ f ∧ f ≤ 5 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t <;> simp only [lieSylowExponent] at hb
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn2 (show 1 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inl rfl, hn2, le_five_of_choose_le (by omega), hf, by omega⟩
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (show 2 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inr rfl, by omega, le_five_of_choose_le (by omega), hf, by omega⟩
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inl rfl, hn2, le_three_of_sq_le (by omega), hf, by omega⟩)
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inr rfl, by omega, le_three_of_sq_le (by omega), hf, by omega⟩)
  · have hn4 : 4 ≤ n := hadm.2.2
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (show 3 ≤ n - 1 by omega)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  · have hn4 : 4 ≤ n := hadm.2.2
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn4 (show 3 ≤ n - 1 by omega)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩)
  · exact Or.inr (Or.inr ⟨by decide, hadm.2.2.1, hf, by omega⟩)

theorem lieModel_card_ne_held (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 4030387200 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 4030387200 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 4030387200 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_held hp hpd with rfl | rfl | rfl | rfl | rfl
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

theorem lieModel_odd_card_ne_L34 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 20160 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 20160 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 20160 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_L34 hp hpd with rfl | rfl | rfl | rfl
  · exact hp2 rfl
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

end CFSG.ComponentClassification.CatLeaf
