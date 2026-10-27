module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Third
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
end Third

@[expose] def C26_2_u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∀ x ∈ T, x * u = u * x
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

@[expose] def S26Act : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∃ ε : ℕ, ε ≤ 1 ∧
            ∀ x ∈ omegaNbrGen Ω K, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (omegaNbrGen Ω K)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
section Claims

@[expose] def S26XProper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W → omegaNbrGen Ω K ≠ ⊤

@[expose] def S26XEdgeless : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        DEdgeless (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K)))

@[expose] def S26XTop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        (⊤ : Subgroup (↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K))) ∉
          oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))

@[expose] def S26XMuZ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∃ W' ∈ WSet (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))),
          MuIsoZ2 (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) W'
end Claims
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
