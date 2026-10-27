module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open

@[expose] def KFactFieldAutEven : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p : ℕ) (α : MulAut J) (T : Subgroup J),
    p.Prime → 5 ≤ p → orderOf α = p → ¬ p ∣ Nat.card J →
    IsSimpleGroup J → ¬ (∀ a b : J, a * b = b * a) → IsKGroup J →
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    (¬ ∃ U : Subgroup J, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧ ∀ g ∈ U, α g = g) →
    Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) = ⊤

@[expose] def KFactFieldAutOdd : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p : ℕ) (α : MulAut J) (U : Subgroup J),
    p.Prime → 5 ≤ p → orderOf α = p → ¬ p ∣ Nat.card J →
    IsSimpleGroup J → ¬ (∀ a b : J, a * b = b * a) → IsKGroup J →
    CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → (∀ g ∈ U, α g = g) →
    Subgroup.closure
      (⋃ (U₀ : Subgroup J) (_ : U₀ ≤ U ∧ U₀ ≠ ⊥), (Subgroup.normalizer (U₀ : Set J) : Set J)) = ⊤

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
