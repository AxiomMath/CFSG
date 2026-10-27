module

public import CFSG.GH74.GLS.Stage2.Local.P34Stmt

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34

@[expose] def Ivk93Kind (k : Kind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) →
      PerfInJ H → HasTwoInvolutionClasses (HBar H) → C0 z k S H ∨ FUS H

theorem ivk93_of_kinds (h : ∀ k : Kind, Ivk93Kind k) : IVK93 :=
  fun G _ _ z k S hctx => h k G z S hctx

end CFSG.GH74.GLS.IVK.Proofs2
