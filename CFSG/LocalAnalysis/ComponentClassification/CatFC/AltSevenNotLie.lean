module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Order
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem card_alternatingGroup_fin_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem eq_of_sylow_mul_eq_three {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (h : lieSylowExponent t n * f = 3) :
    (t = .PSL ∧ n = 2 ∧ f = 3) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) := by
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 3 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
      omega
    have hn4 : n ≤ 3 := by
      by_contra hlt
      have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩
    · exact Or.inr ⟨rfl, rfl, by norm_num at h; omega⟩
  case PSU =>
    obtain ⟨-, -, hn, hn3⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 3 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
      omega
    have hn4 : n ≤ 3 := by
      by_contra hlt
      have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    obtain rfl : n = 3 := by omega
    obtain rfl : f = 1 := by norm_num at h; omega
    exact (hn3 (by norm_num)).elim
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have := Nat.mul_le_mul h4 hf
    omega
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals simp only [lieSylowExponent] at h; omega

theorem not_lieModel_two_card_2520 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {Y : Type} [Group Y] (hcard : Nat.card Y = 2520) {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hY : CFSG.Blueprint.LieModel Y t n 2 f) : False := by
  obtain ⟨-, hM, -⟩ := hO Y t n 2 f hadm hY
  rw [hcard] at hM
  have hT := CFSG.SeitzReduction.CrossChar.ordProj_two_eq_of_two hadm hM
  rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
    CFSG.SeitzReduction.RankOne.LieOdd.ordProj_two_pow_mul_odd (by decide)] at hT
  have hNf : lieSylowExponent t n * f = 3 := (Nat.pow_right_injective le_rfl hT).symm
  rcases eq_of_sylow_mul_eq_three hadm hNf with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · revert hM
    decide
  · revert hM
    decide

theorem not_lieModel_of_alt7 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {Y : Type} [Group Y] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f)
    (hY : CFSG.Blueprint.LieModel Y t n p f) : ¬ Nonempty (Y ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  have hcard : Nat.card Y = 2520 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_seven]
  by_cases hp2 : p = 2
  · subst hp2
    exact not_lieModel_two_card_2520 hO hcard hadm hY
  · exact CFSG.ClassicalInvolution.Hat2A7E5.lieModel_odd_card_ne_A7 hO hp2 hadm hY hcard

theorem not_oddLieType_alt7 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    ¬ CFSG.Blueprint.OddLieType (alternatingGroup (Fin 7)) := by
  rintro ⟨t, n, p, f, -, hp2, hadm, hY⟩
  exact CFSG.ClassicalInvolution.Hat2A7E5.lieModel_odd_card_ne_A7 hO hp2 hadm hY
    card_alternatingGroup_fin_seven

theorem not_evenLieType_alt7 (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    ¬ CFSG.Blueprint.EvenLieType (alternatingGroup (Fin 7)) := by
  rintro ⟨t, n, f, hadm, hY⟩
  exact not_lieModel_two_card_2520 hO card_alternatingGroup_fin_seven hadm hY

end CFSG.ComponentClassification.CatFC
