module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def OuterFixedRankDefAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f →
    CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits → ∀ p : ℕ, p.Prime → 5 ≤ p → ℓ = p →
    ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      2 ≤ CFSG.Open.pRank p (fixedSubgroup α) ∨ (t = .PSL ∧ n = 2 ∧ f = p)

@[expose] def OuterFixedRankCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f →
    CFSG.Blueprint.LieModel K t n ℓ f → t ≠ .Tits → ∀ p : ℕ, p.Prime → 5 ≤ p → ℓ ≠ p →
    ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) → ∀ α : MulAut K, α ^ p = 1 → α ∉ inner K →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) → 2 ≤ CFSG.Open.pRank p (fixedSubgroup α)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
