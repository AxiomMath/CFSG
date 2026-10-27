module

public import CFSG.ClassicalInvolution.Q3.Q3T6D8A
import CFSG.ClassicalInvolution.Asc77.AscT3VHexYEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement Pointwise

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

theorem Std20Three.v_hexY (d : Std20Three K K' J S R R' W V z t) :
    ∃ X : Subgroup G, X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G)) ∧
      X ≤ pairNormalizers K J z t ∧
      pairNormalizers K J z t ≤ Subgroup.normalizer (X : Set G) ∧
      X = oddCoreOf X ⊔ W ∧
      pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) ≤ X ∧
      (∃ r ∈ K ⊓ (S : Subgroup G), ∃ r' ∈ K' ⊓ (S : Subgroup G),
        r ∈ pairNormalizers K J z t ∧ r' ∈ pairNormalizers K J z t ∧ r * t * r⁻¹ = z * t ∧
        (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
        pairNormalizers K J z t ⊓ Subgroup.centralizer
            ((Subgroup.closure {z, t} : Subgroup G) : Set G) = X ⊔ Subgroup.zpowers (r * r')) ∧
      ∃ φ : ↥(pairNormalizers K J z t) →* DihedralGroup 6, Function.Surjective φ ∧
        φ.ker = X.subgroupOf (pairNormalizers K J z t) := by
  exact d.late_toG.v_hexY

theorem Std20Three.v_Y_odd (d : Std20Three K K' J S R R' W V z t) {g x : G}
    (hgY : g ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgz : g * z * g⁻¹ = z)
    (hgt : g * t * g⁻¹ = t) (hxY : x ∈ pairNormalizers K J z t)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hx : Odd (orderOf x)) :
    x⁻¹ * (g * x * g⁻¹) ∈ pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) := by
  obtain ⟨X, -, hXY, hYX, hXeq, hf, ⟨r, hr, r', hr', hrY, hr'Y, hrt, hinv, hcent⟩, φ, hφs,
    hφk⟩ := d.v_hexY
  refine Y_odd_aux φ hφk hXY hYX hXeq hf hrY hr'Y hinv hcent
    (pairNormalizers_le_normalizer K J z t) d.late_hWc ?_
    (fun w hw w2 => d.late_inv_W w hw w2) d.late_z_mem_W d.late_t_mem_W hgY hgW hgz hgt hxY hxW hx
  intro w hw
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨w, d.hWS hw⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
