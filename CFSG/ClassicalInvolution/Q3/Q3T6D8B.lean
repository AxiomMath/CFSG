module

import CFSG.ClassicalInvolution.Asc77.AscT3CLate8BEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DHexMain
public import CFSG.ClassicalInvolution.Q3.Q3T6DSwap

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

private theorem Std20Three.late_toG8B (d : Std20Three K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20Three.late_stepA (d : Std20Three K K' J S R R' W V z t)
    (hc7 : centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) : x ∈ R' := by
  exact d.late_toG8B.late_stepA hc7 hx

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
