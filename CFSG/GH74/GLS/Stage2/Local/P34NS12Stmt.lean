module

public import CFSG.GH74.GLS.Stage2.Local.P34Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

@[expose] def NSm12H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.m12 S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
      HasTwoInvolutionClasses (HBar H) →
      ∀ x ∈ Cen z, IsNonCentralInvolution x → ¬ Group.IsSolvable ↥(Jx x ⊓ H)

end CFSG.GH74.GLS.Stage2.Local.P34
