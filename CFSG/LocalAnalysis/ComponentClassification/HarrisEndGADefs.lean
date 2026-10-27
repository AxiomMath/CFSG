module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public section

namespace CFSG.ComponentClassification.TBLit

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

@[expose] def GriessMultipliersOdd : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), CFSG.Models.LieModel X t n p f →
    p ≠ 2 → (t = .PSL ∨ (t = .PSU ∧ Even n)) →
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)

theorem GriessMultipliersOdd.of_allModels (h : GriessMultipliersAllModels) :
    GriessMultipliersOdd :=
  fun X _ t n p f hm _ _ => h X t n p f hm

end CFSG.ComponentClassification.TBLit
