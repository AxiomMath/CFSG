module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

private lemma six_le_lieSylowExponent {τ : StatedLieTag} {n : ℕ}
    (hτ : (τ = .PSL ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSU ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSp ∧ 3 ≤ n) ∨
      (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7) :
    6 ≤ lieSylowExponent τ n := by
  rcases hτ with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl
  · rcases hn with rfl | rfl <;> norm_num [lieSylowExponent]
  · rcases hn with rfl | rfl <;> norm_num [lieSylowExponent]
  · rw [lieSylowExponent]
    nlinarith
  · rcases hn with rfl | rfl <;> norm_num [lieSylowExponent]
  · norm_num [lieSylowExponent]

theorem not_inChev2_of_classBShape
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) {Q : Type} [Group Q]
    {τ : StatedLieTag} {n : ℕ} (hm : Blueprint.LieModel Q τ n 3 1)
    (hτ : (τ = .PSL ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSU ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSp ∧ 3 ≤ n) ∨
      (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7) :
    ¬ GH74.GLS.InChev2 Q := by
  have hadm' : StatedLieAdmissible τ n 3 1 := Blueprint.LieModel.admissible hm
  have hsix : 6 ≤ lieSylowExponent τ n := six_le_lieSylowExponent hτ
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  intro h
  rcases h with hEven | hA | hU
  ·
    obtain ⟨t, m, f, hadm, hX⟩ := hEven
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' h32
        (hO Q t m 2 f hadm hX).2.1 (hO Q τ n 3 1 hadm' hm).2.1 with
      ⟨-, -, -, -, -, h5⟩ | ⟨-, -, -, -, -, h7⟩ | ⟨-, -, -, hpsp, hn2, -⟩
    · exact absurd h5 (by norm_num)
    · exact absurd h7 (by norm_num)
    · subst hpsp
      rcases hτ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · omega
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  ·
    obtain ⟨e⟩ := hA
    have hcard : Nat.card Q = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hfac := (hO Q τ n 3 1 hadm' hm).2.2
    have hnz : Nat.card Q ≠ 0 := by rw [hcard]; norm_num
    have hge : 6 ≤ (Nat.card Q).factorization 3 := by
      rw [hfac]; simpa using hsix
    have hdvd : 3 ^ 6 ∣ Nat.card Q :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hnz).2 hge
    rw [hcard] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    norm_num at hle
  ·
    have hfacU := (hO Q .PSU 3 3 1 (Blueprint.LieModel.admissible hU) hU).2.2
    have hfac := (hO Q τ n 3 1 hadm' hm).2.2
    rw [hfacU] at hfac
    have hU3 : lieSylowExponent .PSU 3 * 1 = 3 := by norm_num [lieSylowExponent]
    rw [hU3] at hfac
    simp only [mul_one] at hfac
    omega

end CFSG.OddStandard.HigherRank.F3.Ident
