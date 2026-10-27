module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoLocalInclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddLie

open CFSG.Assembly.LowTwoRank
open ClassicalModelStatedBridge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup (GeneralizedFitting.subgroup G)]

theorem odd_classical_index_two_B_under_proper_subgroup_B
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2) (t : StatedLieTag) (n p f : ℕ)
    (hp : p ≠ 2) (hmodel : StatedClassicalModel (GeneralizedFitting.subgroup G) t n p f)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  have : Fact p.Prime := ⟨hmodel.1.1⟩
  cases t with
  | PSL =>
    have hn : 2 ≤ n := hmodel.1.2.2.1
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact CatalogueBLinearTwoLocal.odd_linear_two_generalizedFitting_B_inclusion hnonab p f
        ((Fact.out : p.Prime).odd_of_ne_two hp) (classicalModel_psl_of_stated hmodel) hindex
    · exact CatalogueBLinearHigherB.odd_higher_linear_index_two_B_under_proper_subgroup_B
        hnonab hindex n p f hp h (classicalModel_psl_of_stated hmodel) hproper
  | PSU =>
    exact CatalogueBUnitaryB.odd_unitary_index_two_B_under_proper_subgroup_B hnonab hindex n p f
      hp hmodel.1.2.2.1 (classicalModel_psu_of_stated hmodel) hproper
  | PSp =>
    exact CatalogueBSymplecticB.odd_symplectic_index_two_B_under_proper_subgroup_B hnonab hindex
      n p f hp hmodel.1.2.2.1 (classicalModel_psp_of_stated hmodel) hproper
  | POmegaOdd =>
    exact CatalogueBOrthogonalIndexTwoB.odd_orthogonal_index_two_B_of_stated hnonab hindex
      .POmegaOdd (.inl rfl) n p f hp hmodel hproper
  | POmegaPlus =>
    exact CatalogueBOrthogonalIndexTwoB.odd_orthogonal_index_two_B_of_stated hnonab hindex
      .POmegaPlus (.inr (.inl rfl)) n p f hp hmodel hproper
  | POmegaMinus =>
    exact CatalogueBOrthogonalIndexTwoB.odd_orthogonal_index_two_B_of_stated hnonab hindex
      .POmegaMinus (.inr (.inr rfl)) n p f hp hmodel hproper
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hmodel.2.elim

end CFSG.ComponentClassification.CatalogueBOddLie
