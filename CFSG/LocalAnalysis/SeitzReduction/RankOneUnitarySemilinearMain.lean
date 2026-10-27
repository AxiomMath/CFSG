module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearChar
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearFour
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoMain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem omega_regular_of_semilinear_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 ∧
      HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range :=
  h.omega_regular_of_charInputThree_of_card_sylow' hS2 hR hstar u3CharInputThree_holds
    u3FourNormalizerInput_holds hc

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
