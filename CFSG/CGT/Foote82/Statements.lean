module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

@[expose] def FooteSixF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → IsCharTwoType G → evenRank G = 3 →
      ∀ M L : Subgroup G, GLBIsMaxTwoLocal M → IsFooteBlock M L → IsFType L → InFooteB L

@[expose] def FooteFiveF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → IsCharTwoType G → evenRank G = 3 →
      ∀ J : Subgroup G, InFooteBStar J → IsFType J →
        ∃ M : Subgroup G, GLBIsMaxTwoLocal M ∧ IsFooteBlock M J ∧
          ∀ M' : Subgroup G, GLBIsMaxTwoLocal M' → J ≤ M' → M' = M

@[expose] def FooteSevenSharpF : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → IsCharTwoType G → evenRank G = 3 →
      ∀ J₁ J₂ : Subgroup G, InFooteB J₁ → InFooteB J₂ → J₁ ≠ J₂ → FooteArrow J₁ J₂ →
        IsFType J₁ → IsFType J₂

end CFSG.CGT.Foote82
