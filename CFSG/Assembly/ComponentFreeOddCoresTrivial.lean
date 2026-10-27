module

public import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.Assembly.OddCoreElimination.Coverage
public import CFSG.Assembly.OddCoreElimination.Preparation
public import CFSG.Assembly.OddCoreElimination.CentralizerContainment
public import CFSG.Assembly.OddCoreElimination.FusionControl
public import CFSG.Assembly.OddCoreElimination.FourSpan
public import CFSG.Assembly.OddCoreElimination.Nonisolated
public import CFSG.Assembly.OddCoreElimination.StrongEmbedding

public section

namespace CFSG.Assembly.Dichotomy

theorem oddCore_centralizer_eq_bot_of_componentFree (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hcomp : ¬ IsComponentType G) (hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M)
    (t : G) (ht : orderOf t = 2) :
    oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
  component_free_oddCore_eq_bot_of_steps perfectInvolutionCoverage completedSpanPreparation
    centralInvolutionCentralizer fusionControl
    (fourSpanEqualization_of_nonisolated nonisolatedConjugate)
    (commonSpanStrongEmbedding_of_coverage perfectInvolutionCoverage) hnonab hrank hcomp hse t ht

end CFSG.Assembly.Dichotomy
