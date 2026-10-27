module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4D
import CFSG.ClassicalInvolution.Q3.Q3CLMirror

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  conj_mem_nbrLayer conj_mem_oddCoreOf_of_mem_self)
open scoped commutatorElement

section Fusion


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_mem_conj_sylow (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hs' := T8R.Std8.conj hs n
  have hY' := thin_conj hΩ hY n
  have hV := extraTrans hs' hY'
  exact Q3CL.T8R.Loc.eq_of_mem_conj_sylow_of hs.toFrame hs'.toFrame (T8R.R_ne_T hs')
    (fix_or_swap hs' hY') (eq_of_swap hs' hY' hV) (eq_of_centralizes hs' hY' hV)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _, conj_zt_mul_inv_mem_oddCoreOf hs hY hy⟩)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _,
      conj_zt_mul_inv_mem_oddCoreOf (T8R.Std8.symm' hs) (thin_swap hs hY) hy⟩)
    (Q3CL.l9_3 (T8.partIHyp_of_std8 hs)) hzP htP

theorem outerFusion (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) :
    T8R.OuterFusion K J S R T z t := by
  exact Q3CL.T8R.Loc.outerFusion_of hs.toFrame (conj_zt_of_mem_sylow hs hY)
    (eq_of_mem_conj_sylow hs hY)

theorem false_of_thinLayer_aux [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z))
    (hV : T8R.ExtraTrans Ω K J S z t)
    (hV' : T8R.ExtraTrans Ω J K S t z) (hO : T8R.OuterFusion K J S R T z t) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have haa : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hza : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact haa) ?_
    intro h
    have hzt : z ≠ t := by
      intro h'
      exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
    exact hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have haS := T8R.zt_mem_sylow hs
  obtain ⟨g, hgS, hgne⟩ := Asc77.T8R.exists_conj_mem_sylow_ne (T8R.exists_not_comm hs) S haS
    (fun s hs' => by
      have := conj_zt_of_mem_sylow hs hY hs'
      calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
        _ = (z * t) * s := by rw [this]) hza
  apply hgne
  rcases fix_or_swap hs hY hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact eq_of_centralizes hs hY hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact eq_of_centralizes_J hs hY hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact eq_of_swap hs hY hV hgS hR

theorem false_of_thinLayer [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) : False :=
  false_of_thinLayer_aux hs hY (extraTrans hs hY)
    (extraTrans (T8R.Std8.symm' hs) (thin_swap hs hY)) (outerFusion hs hY)

end Fusion

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4
