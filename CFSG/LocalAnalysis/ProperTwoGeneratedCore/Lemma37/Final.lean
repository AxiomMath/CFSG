module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderCoverStatement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Induction

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem benderCoverStatement : BenderCoverStatement :=
  fun _ _ _ hperf hZ2 hB => bender_cover_quotient hperf hZ2 hB

theorem aschbacher_proper_two_generated_core_of_square_parts
    (h1 : SquareCaseRankOneImpossible)
    (hK : SquareCaseHighRankCentralizerImpossible) (hQ : SquareCaseQuasisimpleImpossibleBelow)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hrank : 3 ≤ CFSG.Open.pRank 2 (S : Subgroup G))
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤) :
    properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* properTwoGenCoreJ1) :=
  aschbacher_proper_two_generated_core_of_below h1 hK hQ jankoConfigurationJOne G hnonab S hrank
    hcore

end CFSG.ProperTwoGeneratedCore.Lemma37
