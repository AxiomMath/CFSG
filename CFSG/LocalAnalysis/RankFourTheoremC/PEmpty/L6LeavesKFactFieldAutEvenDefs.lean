module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FixedLowerBoundAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n ℓ f f₀ p : ℕ), StatedLieAdmissible t n ℓ f →
    LieModel K t n ℓ f → t ≠ .Tits → p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K →
    ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) → f = p * f₀ → ∀ α : MulAut K, α ^ p = 1 →
    α ∉ inner K →
      lieOrderNumerator t n (ℓ ^ f₀) ∣ lieOrderDivisor t n (ℓ ^ f₀) * Nat.card (fixedSubgroup α)

@[expose] def OvergroupLocalAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n f f₀ p : ℕ), StatedLieAdmissible t n 2 f → LieModel K t n 2 f → t ≠ .Tits →
    p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K → ¬ p ∣ lieOrderDivisor t n (2 ^ f) → f = p * f₀ →
    ∃ r : ℕ, r.Prime ∧ ∀ T Y : Subgroup K, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → T ≤ Y →
      Y ≠ ⊤ →
      padicValNat r (Nat.card Y) + padicValNat r (lieOrderDivisor t n (2 ^ f₀)) <
        padicValNat r (lieOrderNumerator t n (2 ^ f₀))

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
