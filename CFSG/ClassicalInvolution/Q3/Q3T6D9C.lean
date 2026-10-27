module

public import CFSG.ClassicalInvolution.Q3.Q3T6DHexMain
import CFSG.ClassicalInvolution.Asc77.AscT3CLate9CEng
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

private theorem Std20Three.late_toG (d : Std20Three K K' J S R R' W V z t) :
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

theorem Std20Three.late_S_act_z (d : Std20Three K K' J S R R' W V z t) {g : G}
    (hg : g ∈ (S : Subgroup G)) : g * z * g⁻¹ = z := by
  exact d.late_toG.late_S_act_z hg

theorem Std20Three.late_members_of_inv (d : Std20Three K K' J S R R' W V z t) {m e : G}
    (hme : m * z * m⁻¹ = e) {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K)
    (hLe : IsUniqueInvolution L e) : L = conjSub m K ∨ L = conjSub m K' := by
  exact d.late_toG.late_members_of_inv hme hL hLe

theorem Std20Three.late_member_data (d : Std20Three K K' J S R R' W V z t) (m : G) :
    conjSub m K ∈ CoreAssembly.conjClass K ∧ conjSub m K' ∈ CoreAssembly.conjClass K ∧
      conjSub m K ≠ conjSub m K' ∧ IsUniqueInvolution (conjSub m K) (m * z * m⁻¹) ∧
      IsUniqueInvolution (conjSub m K') (m * z * m⁻¹) := by
  exact d.late_toG.late_member_data m

theorem Std20Three.late_two_lines (d : Std20Three K K' J S R R' W V z t) {a₀ α b₁ b₂ : G}
    (ha₀ : a₀ ≠ 1) (ha₀2 : a₀ * a₀ = 1) (hα : α ∈ W) (hb₁ : b₁ ∈ W) (hb₂ : b₂ ∈ W)
    (hαa : α * α = a₀) (hb₁a : b₁ * b₁ = a₀) (hb₂a : b₂ * b₂ = a₀)
    (hne : Subgroup.zpowers b₁ ≠ Subgroup.zpowers b₂) :
    Subgroup.zpowers α = Subgroup.zpowers b₁ ∨ Subgroup.zpowers α = Subgroup.zpowers b₂ := by
  exact d.late_toG.late_two_lines d.late_zt_comm ha₀ ha₀2 hα hb₁ hb₂ hαa hb₁a hb₂a hne

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
