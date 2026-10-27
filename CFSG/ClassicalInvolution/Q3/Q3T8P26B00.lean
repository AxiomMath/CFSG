module

public import CFSG.ClassicalInvolution.Q3.Q3T8NDef

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem alphaOf_eq_of_omegaNbr_frame [Fact AlphaFrame3] [IsSimpleGroup G] {K : Subgroup G}
    (hst : AscStand Ω K) (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    (hframe : ∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀) {z : G} (hz : IsUniqueInvolution K z)
    {J₁ J₂ : Subgroup G} {t₁ t₂ : G} (h1 : IsUniqueInvolution J₁ t₁)
    (h2 : IsUniqueInvolution J₂ t₂) (hJ₁ : J₁ ∈ omegaNbr Ω K) (hJ₂ : J₂ ∈ omegaNbr Ω K) :
    alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({t₁, z} : Set G)) :=
  (Fact.out : AlphaFrame3) G Ω K hst hnt hframe z hz J₁ hJ₁ J₂ hJ₂ t₁ t₂ h1 h2

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8U

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77


@[expose] def W2CaseB3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (Q3T7.layerFam3 Ω (z * t)) → False

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8X
