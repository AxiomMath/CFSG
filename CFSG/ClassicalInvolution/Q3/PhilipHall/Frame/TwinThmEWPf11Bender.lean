module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section BenderFam

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

@[expose] def E178U3Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        IsSimpleGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
        (∃ x ∈ Subgroup.normalClosure ({z} : Set G), ∃ y ∈ Subgroup.normalClosure ({z} : Set G),
          x * y ≠ y * x) →
        Subgroup.centralizer ((Subgroup.normalClosure ({z} : Set G) : Subgroup G) : Set G) = ⊥ →
        (∃ n : ℕ, Nonempty (↥(Subgroup.normalClosure ({z} : Set G)) ≃* Theory.Comparator.PSU3Model n)) →
        BenderSuzuki.IsStronglyEmbeddedOrder (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) →
        False

end BenderFam

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
