module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

structure D1Global (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : 4 ≤ evenRank G
  pre : GLBPreuniqueness G

structure D1Local {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop where
  beta : p ∈ GLBBetaFour G
  maxLocal : GLBIsMaxTwoLocal M
  core : GLBWeakCore p (P : Subgroup G) ≤ M

@[expose] def D1MaxCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H : Subgroup G, GLBIsMaxTwoLocal H → ∀ R : Sylow p H,
        (R : Subgroup H).map H.subtype ≤ P → 3 ≤ pRank p ((R : Subgroup H).map H.subtype) →
        H ≤ M

end CFSG.AGLEmbedding
