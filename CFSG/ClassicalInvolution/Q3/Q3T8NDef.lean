module

public import CFSG.ClassicalInvolution.Q3.Q3NLFrame
public import CFSG.ClassicalInvolution.Q3.Q3T7Layer
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson

@[expose] def C27_YnE43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W → Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K

@[expose] def C27_Oab3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          (∀ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J → ∀ z' : G, IsUniqueInvolution K' z' →
            z' ≠ z * t) →
            oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) ≤ sigmaNorm Ω K

@[expose] def C27_Ysmall3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W →
        (¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) →
          ¬ T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)) →
            Q3NL.exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K

@[expose] def AlphaFrame3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand Ω K → (∀ K' ∈ twinSet Ω K, K' = K) → (∃ A₀ : Subgroup G, Q3NL.FuzzyFrame3 Ω A₀) →
      ∀ z : G, IsUniqueInvolution K z → ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K, ∀ t₁ t₂ : G,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₂, z} : Set G)) =
            alphaOf (Subgroup.closure ({t₁, z} : Set G))

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
