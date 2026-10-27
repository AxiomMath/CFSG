module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem eq_five_of_catSL2Hyp_two (hGLS : GLS3OddLieAutComponentsInput) {J : Type} [Group J]
    [Finite J] {t : StatedLieTag} {m p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t m p f) (hJm : LieModel J t m p f) {τ : MulAut J}
    (h : CatSL2Hyp J τ 2) : p = 5 := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  rcases hGLS J t m p f hp hp2 hadm hJm τ hτ D hD with ⟨t', n', f', hadm', hm'⟩ |
      ⟨-, -, -, hL⟩
  · have hadm2 := CrossChar.statedLieAdmissible_of_lieModel hDm
    have hT' : t' ≠ .Tits := by
      rintro rfl
      exact hp2 hadm'.2.2.2.1
    rcases CrossChar.crossChar_arith hadm2 hadm' hp2
        (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm2 hDm (by decide))
        (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm' hm' hT') with
      ⟨-, -, -, -, -, h5⟩ | ⟨-, h3, -⟩ | ⟨h1, -⟩
    · have hf' : f' ≠ 0 := by have := hadm'.2.1; omega
      have hdvd : p ∣ 5 := h5 ▸ dvd_pow_self p hf'
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd
    · omega
    · exact absurd h1 (by decide)
  · exfalso
    have hDs : IsSimpleGroup D := LinearPilot.isSimpleGroup_of_lieModel_PSL hL
    have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1 hDs
    have h1 := card_of_lieModel_PSL_two_two
      (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hL)
    rw [card_of_lieModel_PSL_two_two hDm] at h1
    exact absurd h1 (by decide)

theorem autTwoBound_two_of_L2_25 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (h : LieModel J .PSL 2 5 2) : AutTwoBound J 2 := by
  obtain ⟨hcard, -, -, hO, -⟩ := LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    J 2 5 2 (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)
  have hc : Nat.card J = 2 ^ 3 * 975 := by rw [hcard]; decide
  have hO4 : Nat.card (Outer J) ≤ 4 := Nat.le_of_dvd (by norm_num) ((hO rfl).trans (by decide))
  exact autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna) (by decide) hc.dvd hO4
    (by norm_num)

theorem autTwoBound_two_of_L3_5 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (h : LieModel J .PSL 3 5 1) : AutTwoBound J 2 := by
  obtain ⟨hcard, -, -, -, hO⟩ := LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    J 3 5 1 (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)
  have hc : Nat.card J = 2 ^ 5 * 11625 := by rw [hcard]; decide
  have hO2 : Nat.card (Outer J) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) ((hO (by norm_num)).trans (by decide))
  exact autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna) (by decide) hc.dvd hO2
    (by norm_num)

theorem statedClassicalModel_of_lieModel_PSU {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSU n p f) : StatedClassicalModel X .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem autTwoBound_two_of_U3_5 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (h : LieModel J .PSU 3 5 1) : AutTwoBound J 2 := by
  obtain ⟨-, hcard, hO, -, -⟩ := LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound
    J 3 5 1 (statedClassicalModel_of_lieModel_PSU h)
  have hc : Nat.card J = 2 ^ 4 * 7875 := by
    have h1 : (Nat.card J : ℤ) = 126000 := by rw [hcard]; decide
    have h2 : Nat.card J = 126000 := by exact_mod_cast h1
    rw [h2]
    norm_num
  have hO6 : Nat.card (Outer J) ≤ 6 := by rw [hO]; decide
  exact autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna) (by decide) hc.dvd hO6
    (by norm_num)

end CFSG.SeitzReduction.RankOne
