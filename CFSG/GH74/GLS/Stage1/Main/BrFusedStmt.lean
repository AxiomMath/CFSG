module

public import CFSG.GH74.GLS.Stage1.Main.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def BaseBridgeG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Cen2 G z S → G2Term G z S →
    (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
    (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      U ≤ LC z)

@[expose] def BaseBridgeF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Cen2 G z S →
    (∃ ε : Bool, L4U4TermTypeE ε G z S) →
    (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
    (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      U ≤ LC z)

theorem BaseBridgeRest.of_parts (hg : BaseBridgeG2) (hf : BaseBridgeF) : BaseBridgeRest := by
  intro G _ _ z S hcen hT
  rcases hT with h | h
  · exact hg G z S hcen h
  · exact hf G z S hcen h

end CFSG.GH74.GLS.Stage1.Main
