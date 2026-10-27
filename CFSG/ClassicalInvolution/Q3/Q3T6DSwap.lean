module

public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwapEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20Three.late_toF (d : Std20Three K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Three.late_exists_swap (d : Std20Three K K' J S R R' W V z t) :
    ∃ u ∈ (S : Subgroup G), conjSub u K = K' := by
  exact d.late_toF.late_exists_swap

theorem Std20Three.late_swap_data (d : Std20Three K K' J S R R' W V z t) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') :
    conjSub u K' = K ∧ conjSub u R = R' ∧ conjSub u W = W ∧ conjSub u (S : Subgroup G) = S := by
  exact d.late_toF.late_swap_data hu huK

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
