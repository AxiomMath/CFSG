module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Frame

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem cent_le_normalizer' {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K' : Set G) := by
  have h1 := mem_normalizer_iff_conjSub_eq.mp (d.cent_le_normalizer ha)
  exact mem_normalizer_iff_conjSub_eq.mpr ((d.late_conj_iff (d.hSz ha.1)).mp h1)

end Std20Frame

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
