module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexA
import CFSG.ClassicalInvolution.Q3.Q3T6DHexBEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DHexA

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

private theorem Std20Frame.late_toF (d : Std20Frame K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Frame.late_hWc (d : Std20Frame K K' J S R R' W V z t) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  exact d.late_toF.late_hWc

theorem Std20Frame.late_R_mem_D (d : Std20Frame K K' J S R R' W V z t) :
    R ∈ DSet (CoreAssembly.conjClass K) W := by
  exact d.late_toF.late_R_mem_D

theorem Std20Frame.late_R'_mem_D (d : Std20Frame K K' J S R R' W V z t) :
    R' ∈ DSet (CoreAssembly.conjClass K) W := by
  exact d.late_toF.late_R'_mem_D

theorem Std20Frame.late_z_mem_W (d : Std20Frame K K' J S R R' W V z t) : z ∈ W := by
  exact d.late_toF.late_z_mem_W

theorem Std20Frame.late_t_mem_W (d : Std20Frame K K' J S R R' W V z t) : t ∈ W := by
  exact d.late_toF.late_t_mem_W

theorem Std20Frame.late_exists_n (d : Std20Frame K K' J S R R' W V z t) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * z * n⁻¹ = t := by
  exact d.late_toF.late_exists_n
    (fun hR hK hRK hz => late_exists_dDataGen d.late_hΩ d.hW hR hK hRK hz)
    (fun hd hd' hKL hza hnot =>
      late_pairGen d.late_hΩ d.late_cls d.late_hWc hd hd' hKL hza hnot)

theorem Std20Frame.late_JW (d : Std20Frame K K' J S R R' W V z t) :
    J ⊓ W ∈ USet (CoreAssembly.conjClass K) := by
  exact d.late_toF.late_JW d.late_exists_n

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
