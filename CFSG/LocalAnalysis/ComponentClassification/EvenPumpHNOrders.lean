module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem prime_dvd_HN {p : ℕ} (hp : p.Prime) (h : p ∣ 273030912000000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
  have h1 : p ∈ Nat.primeFactors 273030912000000 :=
    Nat.mem_primeFactors.2 ⟨hp, h, by norm_num⟩
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h1

theorem le_five_of_choose_le_fourteen {n : ℕ} (h : n * (n - 1) / 2 ≤ 14) : n ≤ 5 := by
  by_contra hn
  have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul (show 6 ≤ n by omega) (show 5 ≤ n - 1 by omega)
  omega

theorem le_three_of_sq_le_fourteen {n : ℕ} (h : n ^ 2 ≤ 14) : n ≤ 3 := by
  by_contra hn
  have : 4 * 4 ≤ n * n := Nat.mul_le_mul (show 4 ≤ n by omega) (show 4 ≤ n by omega)
  rw [sq] at h
  omega

theorem lie_casework14 {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hb : lieSylowExponent t n * f ≤ 14) :
    (t = .PSL ∨ t = .PSU) ∧ 2 ≤ n ∧ n ≤ 5 ∧ 1 ≤ f ∧ f ≤ 14 ∨
      (t = .PSp ∨ t = .POmegaOdd) ∧ 2 ≤ n ∧ n ≤ 3 ∧ 1 ≤ f ∧ f ≤ 14 ∨
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ n = 4 ∧ f = 1 ∨
      (t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧
        t ≠ .POmegaMinus) ∧ n = 0 ∧ 1 ≤ f ∧ f ≤ 7 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t <;> simp only [lieSylowExponent] at hb
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn2 (show 1 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inl rfl, hn2, le_five_of_choose_le_fourteen (by omega), hf, by omega⟩
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have hpos : 0 < n * (n - 1) / 2 := by
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn3 (show 2 ≤ n - 1 by omega)
      omega
    have h1 := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f hpos
    exact Or.inl ⟨Or.inr rfl, by omega, le_five_of_choose_le_fourteen (by omega), hf, by omega⟩
  · have hn2 : 2 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inl rfl, hn2, le_three_of_sq_le_fourteen (by omega), hf, by omega⟩)
  · have hn3 : 3 ≤ n := hadm.2.2.1
    have h1 := Nat.le_mul_of_pos_right (n ^ 2) (show 0 < f by omega)
    have h2 := Nat.le_mul_of_pos_left f (show 0 < n ^ 2 by positivity)
    exact Or.inr (Or.inl ⟨Or.inr rfl, by omega, le_three_of_sq_le_fourteen (by omega), hf,
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

theorem lieModel_card_ne_HN (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 273030912000000 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 273030912000000 :=
    hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 273030912000000 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_HN hp hpd with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 14) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework14 hadm hb with
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

theorem factorial_div_two_ne_HN (k : ℕ) : k.factorial / 2 ≠ 273030912000000 := by
  intro hk
  rcases le_or_gt k 17 with hk17 | hk18
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le hk17)
    have h17 : (17 : ℕ).factorial / 2 = 177843714048000 := by decide
    omega
  · have := Nat.div_le_div_right (c := 2) (Nat.factorial_le (show 18 ≤ k by omega))
    have h18 : (18 : ℕ).factorial / 2 = 3201186852864000 := by decide
    omega

end CFSG.ComponentClassification.EvenPump
