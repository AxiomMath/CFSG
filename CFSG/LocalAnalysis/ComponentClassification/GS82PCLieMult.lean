module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBTable
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem odd_genericOrders_two {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    Odd ((genericOrders t n 2 f).1 * (genericOrders t n 2 f).2) := by
  have hf : 1 ≤ f := hadm.2.1
  have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hm : Odd (2 ^ f - 1) := by
    obtain ⟨k, hk⟩ := hq
    exact ⟨k - 1, by omega⟩
  have hp : Odd (2 ^ f + 1) := hq.add_one
  cases t <;> simp only [genericOrders, mul_one]
  all_goals first
    | exact odd_one
    | exact hm.of_dvd_nat (Nat.gcd_dvd_right _ _)
    | exact hp.of_dvd_nat (Nat.gcd_dvd_right _ _)
    | exact absurd rfl hadm.2.2.2
    | (rw [if_pos hq]; exact odd_one)
    | (have hn : 1 ≤ n := by have := hadm.2.2; omega
       have hqn : Even ((2 ^ f) ^ n) := (Nat.even_pow' (by omega)).mpr hq
       exact hqn.add_one.of_dvd_nat (Nat.gcd_dvd_right _ _))

theorem even_exceptionalOrders_two {t : StatedLieTag} {n f : ℕ}
    (h : Even ((exceptionalOrders t n 2 f).1 * (exceptionalOrders t n 2 f).2)) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
      (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
      (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) := by
  unfold exceptionalOrders at h
  split at h <;> simp_all <;> decide

theorem even_center_lie_two_cases
    {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) (hO : pPrimeCore 2 Y = ⊥)
    (hZ : center Y ≠ ⊥) {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hm : Blueprint.LieModel (Y ⧸ center Y) t n 2 f) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
      (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
      (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) := by
  obtain ⟨-, ⟨e⟩⟩ := Milestones.cl_lit_griess_schur_multipliers_all_native_models _ t n 2 f hm
  have hdvd := AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hY.1 (MulEquiv.refl _)
  rw [Nat.card_congr e.toEquiv, SectionRank.QTK.CoverB.card_generic_exceptional] at hdvd
  have h2 : 2 ∣ Nat.card (center Y) := by
    obtain ⟨k, hk⟩ := (Sol78.center_isPGroup_two hO).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 2 hk0
  apply even_exceptionalOrders_two
  rw [even_iff_two_dvd]
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.coprime_two_left.mpr (odd_genericOrders_two hadm)) (h2.trans hdvd)

theorem center_eq_bot_of_lieModel_PSU_three_three
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J)
    (hm : Blueprint.LieModel (J ⧸ center J) .PSU 3 3 1) : center J = ⊥ := by
  obtain ⟨-, ⟨e⟩⟩ := Milestones.cl_lit_griess_schur_multipliers_all_native_models _ .PSU 3 3 1 hm
  have hdvd := AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJ (MulEquiv.refl _)
  rw [Nat.card_congr e.toEquiv, SectionRank.QTK.CoverB.card_generic_exceptional] at hdvd
  have h1 : ((genericOrders .PSU 3 3 1).1 * (genericOrders .PSU 3 3 1).2) *
      ((exceptionalOrders .PSU 3 3 1).1 * (exceptionalOrders .PSU 3 3 1).2) = 1 := by
    simp [genericOrders, exceptionalOrders]
  rw [h1, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

end CFSG.ComponentClassification.GS82PumpInputs
