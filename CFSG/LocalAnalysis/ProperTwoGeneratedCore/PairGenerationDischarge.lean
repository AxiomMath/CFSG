module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairGenerationTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoRemaining

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.Assembly

theorem pairCommutatorGenerationTheorem
    (G : Type) [Group G] [Finite G] :
    RankOnePair.PairCommutatorGenerationTheorem G := fun H z h _ hbeta _ ht => by
  rw [← minimalLocalFailureProperPairHull_eq_native]
  exact PairGeneration.pair_generated_hull_eq_top G H z h hbeta ht

theorem pairStabilizerRankOneTheorem_holds
    (G : Type) [Group G] [Finite G] :
    PairStabilizerRankOneTheorem G :=
  pairStabilizerRankOneTheorem_of_generation (PairGeneration.pairGenerationTheorem G)

theorem highRankPairWitnessTheorem_holds
    (G : Type) [Group G] [Finite G] :
    HighRankPairWitnessTheorem G :=
  highRankPairWitnessTheorem (PairGeneration.pairGenerationTheorem G)

theorem highRankPair_class_size_nine_or_twenty_seven_holds
    {G : Type} [Group G] [Finite G]
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    Nat.card (conjugacyWithin H z) = 9 ∨ Nat.card (conjugacyWithin H z) = 27 :=
  highRankPair_class_size_nine_or_twenty_seven hcomm hR1 (highRankPairWitnessTheorem_holds G)
    (noncentral_pair_action (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G)
        suzukiOuterOdd unitaryAutomorphismRealization) h hbeta hrank

theorem highRankPair_class_size_ne_nine_and_twenty_seven_holds
    {G : Type} [Group G] [Finite G]
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    Nat.card (conjugacyWithin H z) ≠ 9 ∧ Nat.card (conjugacyWithin H z) ≠ 27 :=
  highRankPair_class_size_ne_nine_and_twenty_seven hcomm hR1 (highRankPairWitnessTheorem_holds G)
    (noncentral_pair_action (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G)
        suzukiOuterOdd unitaryAutomorphismRealization) h hbeta ht hrank

theorem linearSuzukiHullOddCoreTrivial_holds
    (G : Type) [Group G] [Finite G] :
    LinearSuzukiHullOddCoreTrivial G :=
  linearSuzukiHullOddCoreTrivial (pairCommutatorGenerationTheorem G)

theorem linearSuzukiPointKernelRootClauses_holds
    (G : Type) [Group G] [Finite G] :
    LinearSuzukiPointKernelRootClauses G :=
  linearSuzukiPointKernelRootClauses (pairCommutatorGenerationTheorem G)

theorem linearDegreeNormalizerSolvableTheorem_holds
    (G : Type) [Group G] [Finite G] :
    LinearDegreeNormalizerSolvableTheorem G :=
  linearDegreeNormalizerSolvableTheorem_of_parts (pairCommutatorGenerationTheorem G)
    (linearSuzukiHullOddCoreTrivial_holds G) (linearSuzukiPointKernelRootClauses_holds G)

theorem nonunitaryLinearDegreeTheorem_holds
    (G : Type) [Group G] [Finite G] :
    NonunitaryLinearDegreeTheorem G :=
  nonunitaryLinearDegreeTheorem_of_parts (pairCommutatorGenerationTheorem G)
    (linearSuzukiHullOddCoreTrivial_holds G)

theorem theoremTwo_of_solvable_and_monomial
    (h : ∀ (G : Type) [Group G] [Finite G],
      SolvableLinearCosetNormalizerTheorem G ∧ UnitaryMonomialTheorem G) : TheoremTwo :=
  theoremTwo_of_generation fun G _ _ => ⟨pairCommutatorGenerationTheorem G, (h G).1, (h G).2⟩

theorem aschbacher_proper_two_generated_core_of_steps
    (h : ∀ (G : Type) [Group G] [Finite G],
      SolvableLinearCosetNormalizerTheorem G ∧ UnitaryMonomialTheorem G)
    (hA : CentralCentralizerStep) (hB : HighRankEscapingStep)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  canonical_of_generated_steps (theoremTwo_of_solvable_and_monomial h)
    (generatedCentralizerStep_of_central hA) (escapingCentralizerStep_of_highRank hB) G hnonab S
    hrank hcore

end CFSG.ProperTwoGeneratedCore.HighRankPair
