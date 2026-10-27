module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG CFSG.Assembly.LowTwoRank

theorem le_six_of_choose_le {n : ℕ} (h : n * (n - 1) / 2 ≤ 18) : n ≤ 6 := by
  by_contra hn
  have : 7 * 6 ≤ n * (n - 1) := Nat.mul_le_mul (show 7 ≤ n by omega) (show 6 ≤ n - 1 by omega)
  omega

theorem le_four_of_sq_le {n : ℕ} (h : n ^ 2 ≤ 18) : n ≤ 4 := by
  by_contra hn
  have : 5 * 5 ≤ n * n := Nat.mul_le_mul (show 5 ≤ n by omega) (show 5 ≤ n by omega)
  rw [sq] at h
  omega

theorem lie_casework_le {B : ℕ} (hB : B ≤ 18) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hb : lieSylowExponent t n * f ≤ B) :
    (t = .PSL ∨ t = .PSU) ∧ 2 ≤ n ∧ n ≤ 6 ∧ 1 ≤ f ∧ f ≤ B ∨
      (t = .PSp ∨ t = .POmegaOdd) ∧ 2 ≤ n ∧ n ≤ 4 ∧ 1 ≤ f ∧ f ≤ B ∨
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ n = 4 ∧ f = 1 ∨
      (t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧
        t ≠ .POmegaMinus) ∧ n = 0 ∧ 1 ≤ f ∧ f ≤ 9 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t <;> simp only [lieSylowExponent] at hb
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn2 (show 1 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inl rfl, hn2, le_six_of_choose_le (by omega), hf, by omega⟩
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (show 2 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inr rfl, by omega, le_six_of_choose_le (by omega), hf, by omega⟩
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inl rfl, hn2, le_four_of_sq_le (by omega), hf, by omega⟩)
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inr rfl, by omega, le_four_of_sq_le (by omega), hf, by omega⟩)
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

theorem lieModel_two_card_ne_hs (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 44352000 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 9) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
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

theorem lieModel_two_card_ne_mcl (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 898128000 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 7) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
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

theorem lieModel_two_card_ne_hn (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 273030912000000 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 14) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
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

theorem lieModel_two_card_ne_ru (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 145926144000 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 14) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
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

theorem lieModel_two_card_ne_fi23 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 4089470473293004800 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 18) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
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

end CFSG.ComponentClassification.CatLeaf
