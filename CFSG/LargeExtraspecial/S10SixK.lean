module

public import CFSG.LargeExtraspecial.S10SixJ
public import Certificates.Certificate19952
public import CFSG.LargeExtraspecial.S10SixI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem exists_act_τ₁_sub : ∃ m : M2, act τ₁ m - m = act σ₂ E00 :=
  Certificates.certificate19952.1

theorem act_σ₂_ne : act σ₂ E00 ≠ E00 :=
  Certificates.certificate19952.2

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem finrank_le_four_of_config
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (h7 : 7 ≤ S.width) (F : Frame X) {τ : S.O} (Y : Hyp10 S g τ) (hτN : τ ∈ Nbar S g t)
    (htN : t ∈ Nbar S g τ) (htτ : t ≠ τ) {k : S.M} (hkR : S.ρ k ∈ Rbar S g t)
    (hπk : F.π ⟨S.ρ k, hkR⟩ = σ₂) {x : S.O} (hxL : x ∈ S.Lbar g)
    (hxc : x ∈ S.Lbar ((k : G) * g)) (hxN : x ∈ Nbar S g τ)
    (hπx : F.π ⟨x, Lbar_le_Rbar X.ht hxL⟩ = τ₁) :
    finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 4 := by
  have hth := mem_Lbar_mul_of_mem_Rbar X.H X.ht hkR
  have hxR := Lbar_le_Rbar X.ht hxL
  obtain ⟨m, hm⟩ := exists_act_τ₁_sub
  set w : Vt S g t := F.φ.symm m with hw
  have hcw : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    have h1 : F.φ (resV X.haQ t ⟨x, hxR⟩ w - w) = F.φ (bV hth) := by
      rw [map_sub, F.compat, hπx, hw, LinearEquiv.apply_symm_apply, hm, bV_eq_resV X hkR hth,
        F.φ_resV_aV, hπk]
    have h2 := congrArg Subtype.val (F.φ.injective h1)
    rw [coe_bV] at h2
    simpa [coe_resV_apply] using h2
  obtain ⟨k₂, hk₂, -, hb₂⟩ := Y.exists_pair
  have hcτ : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g τ := by
    rw [← hcw]
    exact (timmesfeld_10_1_two hCE Y hk₂ hb₂).2.2.2.2 x hxN w (Vt_le_Wt_of_mem_Nbar Y hτN w.2)
  have hcP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [← hcw]
    obtain ⟨y, hyQ, hy⟩ := S.exists_cl (w : S.Qt)
    rw [← hy]
    have hya : y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y := by
      rw [← S.polar_cl_eq_zero_iff hyQ X.haQ, hy]
      exact (mem_Wt.mp (Vt_le_Wt X.H X.ht1 (cl_a_mem_Vt X.ht))) _ w.2
    exact X.C.comm_le y ⟨hyQ, mem_centralizer_singleton_iff.mpr hya⟩ x hxL
  have hc0 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ 0 :=
    cl_conj_z_ne_zero S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
  obtain ⟨k', hk'R, hk'c⟩ := exists_point_of_mem_inf hCE X Y h7 htN htτ ⟨cl_mem_Vt hth, hcτ⟩ hc0
  have hLeq : S.Lbar ((k' : G) * g) = S.Lbar ((k : G) * g) :=
    Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
      (conj_mem_QG' S k'.2 X.haQ) hk'c
  obtain ⟨F'⟩ := Y.exists_frame
  have hπk' : act (F'.π ⟨S.ρ k', hk'R⟩) E00 ≠ E00 := by
    intro h
    have hth' := mem_Lbar_mul_of_mem_Rbar Y.H Y.ht hk'R
    have h1 : F'.φ (bV hth') = F'.φ (aV Y.ht) := by
      rw [bV_eq_resV Y hk'R hth', F'.φ_resV_aV, h, F'.base]
    have h2 : S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹) :=
      congrArg Subtype.val (F'.φ.injective h1)
    rw [hk'c] at h2
    have h3 : bV hth = aV X.ht := Subtype.ext h2
    have h4 := congrArg F.φ h3
    rw [bV_eq_resV X hkR hth, F.φ_resV_aV, hπk, F.base] at h4
    exact act_σ₂_ne h4
  exact finrank_commSpace_le_four hCE Y F' hk'R hπk' (by rw [hk'c]; exact hcP) ⟨hxL, hxN⟩
    (by rw [hLeq]; exact hxc)

end CFSG.LargeExtraspecial.S10
