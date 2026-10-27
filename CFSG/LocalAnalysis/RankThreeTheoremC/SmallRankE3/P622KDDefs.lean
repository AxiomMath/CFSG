module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open

@[expose] def KFactFieldAutEvenAt (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (α : MulAut J) (T : Subgroup J),
    q.Prime → orderOf α = q → ¬ q ∣ Nat.card J →
    IsSimpleGroup J → ¬ (∀ a b : J, a * b = b * a) → CFSG.Open.IsKGroup J →
    CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    (¬ ∃ U : Subgroup J, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧ ∀ g ∈ U, α g = g) →
    Subgroup.closure ({g : J | α g = g} ∪ (T : Set J)) = ⊤

@[expose] def KFactFieldAutOddAt (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (α : MulAut J) (U : Subgroup J),
    q.Prime → orderOf α = q → ¬ q ∣ Nat.card J →
    IsSimpleGroup J → ¬ (∀ a b : J, a * b = b * a) → CFSG.Open.IsKGroup J →
    CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → (∀ g ∈ U, α g = g) →
    Subgroup.closure
      (⋃ (U₀ : Subgroup J) (_ : U₀ ≤ U ∧ U₀ ≠ ⊥), (Subgroup.normalizer (U₀ : Set J) : Set J)) = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
