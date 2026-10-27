module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem statedClassicalModel_of_lieModel_PSp {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSp n p f) : StatedClassicalModel X .PSp n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

@[expose] def OddFiveSL2ListFamilyInput (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    ∀ (m f : ℕ), StatedLieAdmissible t m 5 f → LieModel J t m 5 f →
      ∀ τ : MulAut J, CatSL2Hyp J τ 2 →
        LieModel J .PSL 2 5 2 ∨ LieModel J .PSL 3 5 1 ∨ LieModel J .PSU 3 5 1 ∨
          LieModel J .PSp 2 5 1

theorem oddFiveSL2ListFamilyInput_of_not_admissible {t : StatedLieTag}
    (ht : ∀ m f : ℕ, ¬ StatedLieAdmissible t m 5 f) : OddFiveSL2ListFamilyInput t :=
  fun _ _ _ _ _ m f hadm => absurd hadm (ht m f)

theorem oddFiveSL2ListFamilyInput_twistedB2 : OddFiveSL2ListFamilyInput .twistedB2 :=
  oddFiveSL2ListFamilyInput_of_not_admissible fun _ _ h => absurd h.2.2.2.1 (by norm_num)

theorem oddFiveSL2ListFamilyInput_twistedG2 : OddFiveSL2ListFamilyInput .twistedG2 :=
  oddFiveSL2ListFamilyInput_of_not_admissible fun _ _ h => absurd h.2.2.2.1 (by norm_num)

theorem oddFiveSL2ListFamilyInput_twistedF4 : OddFiveSL2ListFamilyInput .twistedF4 :=
  oddFiveSL2ListFamilyInput_of_not_admissible fun _ _ h => absurd h.2.2.2.1 (by norm_num)

theorem oddFiveSL2ListFamilyInput_Tits : OddFiveSL2ListFamilyInput .Tits :=
  oddFiveSL2ListFamilyInput_of_not_admissible fun _ _ h => absurd h.2.2.2.1 (by norm_num)

theorem autTwoBound_two_of_PSp4_5 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (h : LieModel J .PSp 2 5 1) : AutTwoBound J 2 := by
  obtain ⟨hcard, hO, -⟩ := LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound
    J 2 5 1 (statedClassicalModel_of_lieModel_PSp h)
  have hc : Nat.card J = 2 ^ 6 * 73125 := by rw [hcard]; decide
  have hO4 : Nat.card (Outer J) ≤ 4 := Nat.le_of_dvd (by norm_num) (hO.trans (by decide))
  exact autTwoBound_of_card (center_eq_bot_of_simple_nonabelian hJ hna) (by decide) hc.dvd hO4
    (by norm_num)

end CFSG.SeitzReduction.RankOne
