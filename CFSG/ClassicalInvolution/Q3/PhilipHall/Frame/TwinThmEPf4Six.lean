module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section Six

@[expose] def Lemma17_3Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    Q3CL.ClassicalClause Ω →
    (∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2)) →
    (∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) →
    (∀ L ∈ Ω, AEmpty Ω L) → EIH (Nat.card G) → classicalInvolutionOddCore G = ⊥ →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥) → (⨆ J ∈ Ω, J) = ⊤ →
    ∀ K ∈ Ω, (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥

end Six

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
