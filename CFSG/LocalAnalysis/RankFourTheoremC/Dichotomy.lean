module

public import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers

@[expose] def StrongOrExceptional (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
    GLBCore p 2 (P : Subgroup G) ≤ M →
      ((p ∣ Nat.card M ∧ ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G)) ∨
        (5 ≤ p ∧ Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
          ∃ P₀ : Subgroup G, GLBClauseTwo M P P₀ p))

@[expose] def DichotomyRank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G → StrongOrExceptional G

variable {G : Type} [Group G] [Finite G]

theorem almostStrongAtCore_of_dichotomy [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hFC : FullCoreLocality G) (hDich : StrongOrExceptional G) : AlmostStrongAtCore G := by
  intro p P M hloc
  have hcore : GLBCore p 2 (P : Subgroup G) ≤ M := hFC p P M hloc
  exact ⟨hloc.beta, twoLocal_ne_top hnonab hloc.maxLocal.1, hloc.maxLocal.1, P,
    sylow_le_of_core hloc, hcore, hDich p P M hloc hcore⟩

theorem e1Rank4_of_dichotomy (hFC : FullCoreRank4) (hDich : DichotomyRank4) : E1Rank4 :=
  fun G _ _ _ hnonab hK hchar he hpre => almostStrongAtCore_of_dichotomy hnonab
    (hFC G hnonab hK hchar he hpre) (hDich G hnonab hK hchar he hpre)

theorem theoremCRankFour_of_node_endpoints (hD1 : D1Rank4) (hD2 : D2Rank4)
    (hFC : FullCoreRank4) (hδ₂ : DeltaTwoRank4) (hDich : DichotomyRank4)
    (hE2 : E2NonstrongRank4) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) : GLBUniqueFour G :=
  theoremCRankFour_of_refined_endpoints hD1 hD2 hFC hδ₂ (e1Rank4_of_dichotomy hFC hDich) hE2 G
    hnonab hK hchar he hpre

end CFSG.LocalAnalysis.RankFourTheoremC
