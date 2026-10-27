module

public import CFSG.ClassicalInvolution.Q3.Q3T6DC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t)
include d

theorem concl20_5_of_7 (c7 : Concl20_7 S K K' z) : Concl20_5 S K K' z := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.concl20_5_of_7_of d.sup_le_centralizer_z
    ((d.hSz).trans (le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne))
    d.viol.hzK d.z_mem_S c7

end Std20Three

@[expose] def Res20_7Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_7 S K K' z

theorem c20_5_of_res20_7Three (h : Res20_7Three) : C20_5Three := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4
  exact d.concl20_5_of_7 (h G K K' J S R R' W V z t d c3 c4)

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
