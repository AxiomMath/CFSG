module

import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage
public import CFSG.Assembly.Defs

public section

namespace CFSG.Assembly.Dichotomy

theorem derivedInvolutionTransfer :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U : Subgroup G), U ≤ S →
      U.relIndex (S : Subgroup G) = 2 → ∀ t ∈ commutator G, orderOf t = 2 →
        ∃ g : G, g⁻¹ * t * g ∈ U := by
  intro G _ _ S U hUS hindex t htG ht
  exact CFSG.ProperTwoGeneratedCore.derived_involution_sylow_maximal_transfer S U hUS hindex t ht
    htG

end CFSG.Assembly.Dichotomy
