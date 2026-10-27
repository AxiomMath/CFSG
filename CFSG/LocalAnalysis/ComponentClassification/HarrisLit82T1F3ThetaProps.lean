module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def Harris82ThetaBalanceThreeOne : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ((IsSimpleChevalleyOver 3 K ∧ ∀ f : ℕ, ¬ Blueprint.LieModel K .PSL 2 3 f) ∨
      Nonempty (K ≃* ↥Blueprint.NativeSporadic.M11)) → IsThetaBalanced K

@[expose] def Harris82OddCoreThreeTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ (τ : StatedLieTag) (n : ℕ), Blueprint.LieModel X τ n 3 1) →
    ∀ t : X, orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set X)) = ⊥

theorem harris82ThetaBalanceThree_of_split (h1 : Harris82ThetaBalanceThreeOne)
    (h2 : Harris82OddCoreThreeTwo) : Harris82ThetaBalanceThree :=
  ⟨h1, h2⟩

end CFSG.ComponentClassification.HarrisLit.T1
