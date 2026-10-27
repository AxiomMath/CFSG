module

public import CFSG.ClassicalInvolution.Asc77.AscT8RMain
public import CFSG.ClassicalInvolution.Asc77.AscT8RV

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8R

variable (p f : ℕ) [Fact p.Prime]

@[expose] def OuterFusionAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K) →
        OuterFusion K J S R T z t

variable {p f}

theorem c26_1_of_outer (h : OuterFusionAll p f) : C26_1 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hX
  exact false_of_hX hs hX (extraTrans hs hX) (extraTrans (Std8.symm' hs)
    (eq_sup_oddCoreOf_swap hs hX)) (h G Ω K J S R T W z t hs hdisc hX)

end T8R

end CFSG.ClassicalInvolution.Asc77
