module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoRemaining

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem aschbacher_proper_two_generated_core_of_remaining
    (h : ∀ (G : Type) [Group G] [Finite G],
      RankOnePair.PairCommutatorGenerationTheorem G ∧ LinearSuzukiHullOddCoreTrivial G ∧
        LinearSuzukiPointKernelRootClauses G ∧ SolvableLinearCosetNormalizerTheorem G ∧
          UnitaryMonomialTheorem G)
    (hA : CentralCentralizerStep) (hB : HighRankEscapingStep)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  canonical_of_generated_steps (theoremTwo_of_remaining h) (generatedCentralizerStep_of_central hA)
    (escapingCentralizerStep_of_highRank hB) G hnonab S hrank hcore

theorem aschbacher_proper_two_generated_core_of_generation
    (h : ∀ (G : Type) [Group G] [Finite G],
      RankOnePair.PairCommutatorGenerationTheorem G ∧ SolvableLinearCosetNormalizerTheorem G ∧
        UnitaryMonomialTheorem G)
    (hA : CentralCentralizerStep) (hB : HighRankEscapingStep)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  canonical_of_generated_steps (theoremTwo_of_generation h) (generatedCentralizerStep_of_central hA)
    (escapingCentralizerStep_of_highRank hB) G hnonab S hrank hcore

end CFSG.ProperTwoGeneratedCore.HighRankPair
