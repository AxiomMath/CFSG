module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint
open scoped commutatorElement

@[expose] def TwSwap {X : Type} [Group X] (R : Subgroup X) (z : X) : Prop :=
  ∃ g ∈ Subgroup.centralizer ({z} : Set X), ∃ r ∈ R, ⁅g, r⁆ ^ 2 ∉ oddCoreImg R

@[expose] def TwKindL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) → ¬ TightActs3 R z →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
        LieModel (FStarQuot X) .PSL 2 p f → 2 ∣ (genFittingFStar X).index ∧ TwSwap R z

@[expose] def TwKindL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) → ¬ TightActs3 R z →
      (genFittingFStar X).index ∣ 6 → ∀ p f : ℕ, p.Prime → p ≠ 2 →
        LieModel (FStarQuot X) .PSL 3 p f → 2 ∣ (genFittingFStar X).index ∧ TwSwap R z

@[expose] def TwKindU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) → ¬ TightActs3 R z →
      (genFittingFStar X).index ∣ 6 → ∀ p f : ℕ, p.Prime → p ≠ 2 →
        LieModel (FStarQuot X) .PSU 3 p f → 2 ∣ (genFittingFStar X).index ∧ TwSwap R z

@[expose] def TwKindU33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) → ¬ TightActs3 R z →
      (genFittingFStar X).index ∣ 6 → LieModel (FStarQuot X) .PSU 3 3 1 →
        2 ∣ (genFittingFStar X).index ∧ TwSwap R z

end CFSG.ClassicalInvolution.Q3.TL4
