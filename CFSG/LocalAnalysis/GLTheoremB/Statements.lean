module

public import CFSG.LocalAnalysis.GLTheoremB.Defs
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

@[expose] def TheoremB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → ∀ m : ℕ, 4 ≤ m →
      (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
        ∀ p ∈ GLABeta m G, GLAWeakCoreLocal G p ∨ GLADeltaZero G p

@[expose] def TheoremOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → ∀ m : ℕ, 4 ≤ m →
      (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
        ∀ p ∈ GLABeta m G, GLATwoLocalRank p G = m → ¬ GLADeltaZero G p →
          ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧
            lambdaStarGroup p B ≤ M ∧ GLBCore p 3 B ≤ M

@[expose] def TheoremTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → ∀ m : ℕ, 4 ≤ m →
      (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
        ∀ p ∈ GLABeta m G, GLATwoLocalRank p G = m → ¬ GLADeltaZero G p →
          ∀ B M : Subgroup G, IsBOneMax p B → GLAIsMaxTwoLocal M → lambdaStarGroup p B ≤ M →
            GLBCore p 3 B ≤ M →
              (GLAWeakCoreLocal G p ∨ GLADeltaZero G p) ∨
                ∃ θ : Subgroup G → Subgroup G, ∀ D : Subgroup G, IsPPlane p D →
                  IsPGroup 2 (θ D) ∧ (∀ g : G, θ (GLBConj g D) = GLBConj g (θ D)) ∧
                    (D ≤ M → IsTwoConnectedIn p M D B →
                      pCoreOf 2 M ≤ θ D ∧ θ D ≤ M ∧
                        ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ θ D →
                          Subgroup.normalizer (T : Set G) ≤ M)

end CFSG.LocalAnalysis.GLTheoremB
