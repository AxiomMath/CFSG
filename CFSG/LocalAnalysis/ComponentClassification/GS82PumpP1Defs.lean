module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank

@[expose] def OddLieCharUnique : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ) (t' : StatedLieTag) (n' r f' : ℕ),
    p ≠ 2 → r ≠ 2 → Blueprint.LieModel X t n p f → Blueprint.LieModel X t' n' r f' → p = r

@[expose] def ChevOddSporadicClause : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.NativeSporadic.SporadicRep S → ∀ (σ : MulAut S) (P : Subgroup S),
    ProperFixedComponent σ P → ∀ r : ℕ, r.Prime → r ≠ 2 →
    HarrisLit.IsSimpleChevalleyOver r (↥P ⧸ Open.fusionZStar ↥P) →
    ¬ GH74.GLS.InChev2 (↥P ⧸ Open.fusionZStar ↥P) →
      Blueprint.NativeSporadic.IsSporadic S .J3 ∧
        Blueprint.LieModel (↥P ⧸ Open.fusionZStar ↥P) .PSL 2 17 1

end CFSG.ComponentClassification.GS82PumpInputs
