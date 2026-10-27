module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem e16_tags_mul_pred_two {n : ℕ} (h : 2 ≤ n) : 2 ≤ n * (n - 1) := by
  have := Nat.mul_le_mul h (show 1 ≤ n - 1 by omega)
  omega

theorem e16_tags_mul_pred_six {n : ℕ} (h : 3 ≤ n) : 6 ≤ n * (n - 1) := by
  have := Nat.mul_le_mul h (show 2 ≤ n - 1 by omega)
  omega

theorem e16_tags_mul_pred_twelve {n : ℕ} (h : 4 ≤ n) : 12 ≤ n * (n - 1) := by
  have := Nat.mul_le_mul h (show 3 ≤ n - 1 by omega)
  omega

theorem e16_tags_sq_ge_four {n : ℕ} (h : 2 ≤ n) : 4 ≤ n ^ 2 := by
  have := Nat.mul_le_mul h h
  rw [sq]
  omega

theorem e16_sylowExp_pos {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) :
    1 ≤ lieSylowExponent t n := by
  obtain ⟨-, -, h⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -, -⟩ := h
    have := e16_tags_mul_pred_two hn
    show 1 ≤ n * (n - 1) / 2
    omega
  case PSU =>
    obtain ⟨hn, -⟩ := h
    have := e16_tags_mul_pred_six hn
    show 1 ≤ n * (n - 1) / 2
    omega
  case PSp =>
    obtain ⟨hn, -⟩ := h
    have := e16_tags_sq_ge_four hn
    show 1 ≤ n ^ 2
    omega
  case POmegaOdd =>
    obtain ⟨hn, -⟩ := h
    have := e16_tags_sq_ge_four (show 2 ≤ n by omega)
    show 1 ≤ n ^ 2
    omega
  case POmegaPlus =>
    have := e16_tags_mul_pred_twelve (show 4 ≤ n from h)
    show 1 ≤ n * (n - 1)
    omega
  case POmegaMinus =>
    have := e16_tags_mul_pred_twelve (show 4 ≤ n from h)
    show 1 ≤ n * (n - 1)
    omega
  all_goals norm_num [lieSylowExponent]

theorem e16_sylowExp_mul_eq_one {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (h : lieSylowExponent t n * f = 1) :
    t = .PSL ∧ n = 2 ∧ f = 1 := by
  have he : lieSylowExponent t n = 1 := Nat.eq_one_of_mul_eq_one_right h
  have hf : f = 1 := Nat.eq_one_of_mul_eq_one_left h
  obtain ⟨-, -, hrest⟩ := hadm
  clear h
  cases t
  case PSL =>
    obtain ⟨hn, -, -⟩ := hrest
    have he' : n * (n - 1) / 2 = 1 := he
    refine ⟨rfl, ?_, hf⟩
    by_contra hne
    have h6 := e16_tags_mul_pred_six (show 3 ≤ n by omega)
    omega
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    have he' : n * (n - 1) / 2 = 1 := he
    exfalso
    have h6 := e16_tags_mul_pred_six hn
    omega
  case PSp =>
    obtain ⟨hn, -⟩ := hrest
    have he' : n ^ 2 = 1 := he
    exfalso
    have h4 := e16_tags_sq_ge_four hn
    omega
  case POmegaOdd =>
    obtain ⟨hn, -⟩ := hrest
    have he' : n ^ 2 = 1 := he
    exfalso
    have h4 := e16_tags_sq_ge_four (show 2 ≤ n by omega)
    omega
  case POmegaPlus =>
    have he' : n * (n - 1) = 1 := he
    exfalso
    have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    omega
  case POmegaMinus =>
    have he' : n * (n - 1) = 1 := he
    exfalso
    have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    omega
  all_goals (exfalso; norm_num [lieSylowExponent] at he)

theorem e16_even_cases {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : lieSylowExponent t n * f ≤ 4) :
    (t = .PSL ∧ n = 2 ∧ (f = 2 ∨ f = 3 ∨ f = 4)) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, hne1, -⟩ := hrest
    change n * (n - 1) / 2 * f ≤ 4 at h
    have hn3 : n ≤ 3 := by
      by_contra hc
      have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n by omega)
      have hmono := Nat.mul_le_mul (le_refl (n * (n - 1) / 2)) hf
      omega
    rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
    · have e2 : (2:ℕ) * (2 - 1) / 2 = 1 := rfl
      rw [e2, one_mul] at h
      have hf1 : f ≠ 1 := by
        rintro rfl
        exact hne1 (by norm_num)
      left
      refine ⟨rfl, rfl, ?_⟩
      omega
    · have e3 : (3:ℕ) * (3 - 1) / 2 = 3 := rfl
      rw [e3] at h
      right
      refine ⟨rfl, rfl, ?_⟩
      omega
  case PSU =>
    obtain ⟨hn, hne⟩ := hrest
    change n * (n - 1) / 2 * f ≤ 4 at h
    have hn3 : n ≤ 3 := by
      by_contra hc
      have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n by omega)
      have hmono := Nat.mul_le_mul (le_refl (n * (n - 1) / 2)) hf
      omega
    exfalso
    obtain rfl : n = 3 := by omega
    have e3 : (3:ℕ) * (3 - 1) / 2 = 3 := rfl
    rw [e3] at h
    have hf1 : f = 1 := by omega
    subst hf1
    exact hne (by norm_num)
  case PSp =>
    obtain ⟨hn, hne⟩ := hrest
    change n ^ 2 * f ≤ 4 at h
    rw [sq] at h
    have hn2 : n ≤ 2 := by
      by_contra hc
      have h9 := Nat.mul_le_mul (show 3 ≤ n by omega) (show 3 ≤ n by omega)
      have hmono := Nat.mul_le_mul (le_refl (n * n)) hf
      omega
    obtain rfl : n = 2 := by omega
    have e4 : (2:ℕ) * 2 = 4 := rfl
    rw [e4] at h
    have hf1 : f = 1 := by omega
    subst hf1
    exact (hne (by norm_num)).elim
  case POmegaOdd =>
    obtain ⟨-, hp⟩ := hrest
    exact (hp rfl).elim
  case POmegaPlus =>
    exfalso
    change n * (n - 1) * f ≤ 4 at h
    have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    have hmono := Nat.mul_le_mul (le_refl (n * (n - 1))) hf
    omega
  case POmegaMinus =>
    exfalso
    change n * (n - 1) * f ≤ 4 at h
    have h12 := e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    have hmono := Nat.mul_le_mul (le_refl (n * (n - 1))) hf
    omega
  case G2 =>
    exfalso
    change 6 * f ≤ 4 at h
    omega
  case F4 =>
    exfalso
    change 24 * f ≤ 4 at h
    omega
  case E6 =>
    exfalso
    change 36 * f ≤ 4 at h
    omega
  case E7 =>
    exfalso
    change 63 * f ≤ 4 at h
    omega
  case E8 =>
    exfalso
    change 120 * f ≤ 4 at h
    omega
  case twistedE6 =>
    exfalso
    change 36 * f ≤ 4 at h
    omega
  case trialityD4 =>
    exfalso
    change 12 * f ≤ 4 at h
    omega
  case twistedB2 =>
    exfalso
    obtain ⟨-, -, -, hf3⟩ := hrest
    change 2 * f ≤ 4 at h
    omega
  case twistedG2 =>
    obtain ⟨-, hp3, -, -⟩ := hrest
    exact absurd hp3 (by norm_num)
  case twistedF4 =>
    exfalso
    change 12 * f ≤ 4 at h
    omega
  case Tits =>
    exfalso
    change 11 * f ≤ 4 at h
    omega

theorem e16_char5_tag {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 5 f) :
    t ≠ .twistedB2 ∧ t ≠ .twistedG2 ∧ t ≠ .twistedF4 ∧ t ≠ .Tits := by
  obtain ⟨-, -, hrest⟩ := hadm
  cases t
  case twistedB2 =>
    obtain ⟨-, h2, -⟩ := hrest
    exact absurd h2 (by norm_num)
  case twistedG2 =>
    obtain ⟨-, h3, -⟩ := hrest
    exact absurd h3 (by norm_num)
  case twistedF4 =>
    obtain ⟨-, h2, -⟩ := hrest
    exact absurd h2 (by norm_num)
  case Tits =>
    obtain ⟨-, h2, -⟩ := hrest
    exact absurd h2 (by norm_num)
  all_goals decide

end CFSG.ComponentClassification.CatFC
