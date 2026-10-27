module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT3b
import CFSG.ClassicalInvolution.Q3.Q3CLMirror

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_centralizes (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) (hV : ExtraTrans Ω K J S z t)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hn : x * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * x := by
    rw [inv_inv]
    exact hxc
  obtain ⟨O, hO, h1⟩ := conj_zt_mul_inv_mem_of_orderFour hs hC hV (n := g⁻¹) hxK hx4 hn
  rw [inv_inv] at h1
  exact eq_of_mul_inv_mem_odd S.isPGroup' hb (zt_mem_sylow hs) hO h1

theorem eq_of_centralizes_J (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) (hV' : ExtraTrans Ω J K S t z)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxJ : x ∈ J) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hzt : z * t = t * z := Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hs' := Std8.symm' hs
  rw [hzt] at hb hxc ⊢
  exact eq_of_centralizes hs' hC hV' hb hxJ hx4 hxc

theorem false_of_core [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) (hV : ExtraTrans Ω K J S z t)
    (hV' : ExtraTrans Ω J K S t z) (hO : OuterFusion K J S R T z t) : False := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have haa : z * t * (z * t) = 1 := Q3.Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hza : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact haa) ?_
    intro h
    have hzt : z ≠ t := by
      intro h'
      exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
    exact hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have haS := zt_mem_sylow hs
  obtain ⟨g, hgS, hgne⟩ := Asc77.T8R.exists_conj_mem_sylow_ne (exists_not_comm hs) S haS
    (fun s hs' => by
      have := conj_zt_of_mem_sylow hs hC hs'
      calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
        _ = (z * t) * s := by rw [this]) hza
  apply hgne
  rcases fix_or_swap hs hC hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact eq_of_centralizes hs hC hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact eq_of_centralizes_J hs hC hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact eq_of_swap hs hC hV hgS hR
end Cert
end Core
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
    CFSG.ClassicalInvolution.Asc77.T8
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_mem_conj_sylow (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hs' := Std8.conj hs n
  have hV := extraTrans hs' hC
  exact Q3.Q3CL.T8R.Loc.eq_of_mem_conj_sylow_of hs.toFrame hs'.toFrame (R_ne_T hs')
    (fix_or_swap hs' hC) (eq_of_swap hs' hC hV) (eq_of_centralizes hs' hC hV)
    (fun hy => conj_zt_mul_inv_mem_oddCoreOf hs hC hy)
    (fun hy => conj_zt_mul_inv_mem_oddCoreOf (Std8.symm' hs) hC hy)
    (Hat2A7P1.l9_3 (T8.partIHyp_of_std8 hs)) hzP htP

theorem outerFusion (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) : OuterFusion K J S R T z t := by
  exact Q3.Q3CL.T8R.Loc.outerFusion_of hs.toFrame (conj_zt_of_mem_sylow hs hC)
    (eq_of_mem_conj_sylow hs hC)

theorem false_of_core26 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) (hC : Core26All Ω) :
    False :=
  false_of_core hs hC (extraTrans hs hC) (extraTrans (Std8.symm' hs) hC) (outerFusion hs hC)
end Cert
end Core
end T8R
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
