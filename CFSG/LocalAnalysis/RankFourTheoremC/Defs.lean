module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Statements

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

@[expose] def D1Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → D1For G

@[expose] def D2For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ GLBBetaFour G, ∀ (P : Sylow p G) (M : Subgroup G), GLBIsMaxTwoLocal M →
    GLBCore p 2 (P : Subgroup G) ≤ M → ∀ Q : Subgroup G, IsPGroup p Q → pRank p Q = 2 →
      GLBCore p 1 Q ≤ M → ∀ H : Subgroup G, IsTwoLocal H → Q ≤ H → H ≤ M

@[expose] def D2Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBDeltaOne G → GLBDeltaTwo G → D2For G

variable (G : Type) [Group G] [Finite G]

@[expose] def AlmostStrongAtCore : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M → GLBAlmostStrong M p

@[expose] def ConfinementAtCore : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

@[expose] def AlmostStrongMaximalLocals : Prop :=
  ∀ M : Subgroup G, GLBIsMaxTwoLocal M → ∀ p ∈ GLBSigma M, GLBAlmostStrong M p

@[expose] def RankTwoConfinement : Prop :=
  ∀ M : Subgroup G, GLBIsMaxTwoLocal M → ∀ p ∈ GLBSigma M, ∀ H : Subgroup G, IsTwoLocal H →
    2 ≤ pRank p (H ⊓ M) → H ≤ M

@[expose] def E1Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → AlmostStrongAtCore G

@[expose] def E2Rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → ConfinementAtCore G

end CFSG.LocalAnalysis.RankFourTheoremC
