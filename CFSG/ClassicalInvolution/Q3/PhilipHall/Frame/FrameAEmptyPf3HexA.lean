module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3Cfg
import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexAEng

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

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Frame.late_cls (d : Std20Frame K K' J S R R' W V z t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass K) :=
  d.cls

private theorem Std20Frame.late_toF (d : Std20Frame K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Frame.late_isSylow2In_S (d : Std20Frame K K' J S R R' W V z t) :
    IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) := by
  exact d.late_toF.late_isSylow2In_S

theorem Std20Frame.late_nbr (d : Std20Frame K K' J S R R' W V z t) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  exact d.late_toF.late_nbr

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
