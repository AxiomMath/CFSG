module

public import CFSG.LargeExtraspecial.S10SixC
public import CFSG.LargeExtraspecial.S10TwoC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem pf_comm : ∀ m m' : M2, pf m m' = pf m' m := by decide +kernel

theorem exists_pf_sep : ∀ γ : Gm, act γ E00 ≠ E00 →
    ∃ m : M2, pf E00 m = 0 ∧ pf (act γ E00) m = 1 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem orthogonal_clSub_Qa' (H : Hyp4 S g) (C : Cons311 S g) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) =
      S.clSub (S.QG ⊓ S.Qa g) := by
  have hle : S.clSub (S.QG ⊓ S.Qa g) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) :=
    fun v hv u hu => by
      rw [polarBilin_apply_apply]
      exact polar_eq_zero_of_mem_clSub H.conj_ne hu hv
  have hdim := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, S.finrank_Qt_eq_two_mul_width]
  omega

theorem finrank_commSpace_le_four_of_fixW (X : Hyp10 S g t) (F : Frame X)
    {k : S.M} (hkR : S.ρ k ∈ Rbar S g t) (hπk : act (F.π ⟨S.ρ k, hkR⟩) E00 ≠ E00)
    (hcP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g)) {x : S.O}
    (hxL : x ∈ S.Lbar g) (hxW : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    (hxc : x ∈ S.Lbar ((k : G) * g)) :
    finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 4 := by
  have hth := mem_Lbar_mul_of_mem_Rbar X.H X.ht hkR
  have hcV := cl_mem_Vt hth
  have hβ := beta_bV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ hkR hth
  have hβa := beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ
  have hbφ : F.φ (bV hth) = act (F.π ⟨S.ρ k, hkR⟩) E00 := by
    rw [bV_eq_resV X hkR hth, F.φ_resV_aV]
  have haPc : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
    have h1 := (hβa (bV hth)).mpr hcP
    rw [F.beta_eq, F.base, pf_comm, ← F.base, ← F.beta_eq] at h1
    exact (hβ (aV X.ht)).mp h1
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  set Pc := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) with hPc
  set D := Vt S g t ⊓ P ⊓ Pc with hD
  have hspan_a : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ D :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ⟨⟨cl_a_mem_Vt X.ht, cl_mem_clSub_self X.haQ⟩, haPc⟩
  have hspan_c : (ZMod 2) ∙ S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≤ D :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ⟨⟨hcV, hcP⟩, cl_mem_clSub_self (conj_mem_QG' S k.2 X.haQ)⟩
  have hU : (Wt S g t ⊔ P ⊔ Pc).map
      (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤ D := by
    rw [Submodule.map_sup, Submodule.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨y, hyQ, rfl⟩ := S.exists_cl w
      have hya : y * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * y := by
        rw [← S.polar_cl_eq_zero_iff hyQ X.haQ, polar_comm]
        exact (mem_Wt.mp hw) _ (cl_a_mem_Vt X.ht)
      have hyc : y * ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
          (k : G) * g * S.z * ((k : G) * g)⁻¹ * y := by
        rw [← S.polar_cl_eq_zero_iff hyQ (conj_mem_QG' S k.2 X.haQ), polar_comm]
        exact (mem_Wt.mp hw) _ hcV
      exact ⟨⟨hxW _ hw,
        X.C.comm_le y ⟨hyQ, mem_centralizer_singleton_iff.mpr hya⟩ x hxL⟩,
        (X.C.mul k).comm_le y ⟨hyQ, mem_centralizer_singleton_iff.mpr hyc⟩ x hxc⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact hspan_a (Lbar_apply_sub_mem_span' X.haQ hp hxL)
    · rintro _ ⟨p, hp, rfl⟩
      exact hspan_c (Lbar_apply_sub_mem_span' (conj_mem_QG' S k.2 X.haQ) hp hxc)
  have hD2 : finrank (ZMod 2) D ≤ 2 := by
    obtain ⟨m, hm0, hm1⟩ := exists_pf_sep _ hπk
    set v : Vt S g t := F.φ.symm m with hv
    have hvP : (v : S.Qt) ∈ P := by
      rw [← hβa, F.beta_eq, F.base, hv, LinearEquiv.apply_symm_apply]
      exact hm0
    have hvPc : (v : S.Qt) ∉ Pc := by
      rw [← hβ, F.beta_eq, hbφ, hv, LinearEquiv.apply_symm_apply, hm1]
      exact one_ne_zero
    have hlt : D < Vt S g t ⊓ P := by
      refine lt_of_le_of_ne inf_le_left fun h => hvPc ?_
      have : (v : S.Qt) ∈ Vt S g t ⊓ P := ⟨v.2, hvP⟩
      rw [← h] at this
      exact this.2
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := finrank_clSub_inf_Vt X.H X.C X.ht X.ht1 X.hVQ
    rw [X.h4, ← hP, inf_comm P (Vt S g t)] at h2
    omega
  have hperp : LinearMap.BilinForm.orthogonal S.q.polarBilin (Wt S g t ⊔ P ⊔ Pc) = D := by
    rw [orthogonal_sup_eq, orthogonal_sup_eq, orthogonal_Wt, hP, hPc,
      orthogonal_clSub_Qa' X.H X.C, orthogonal_clSub_Qa' (X.H.mul k) (X.C.mul k)]
  have h3 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (Wt S g t ⊔ P ⊔ Pc)
  rw [hperp] at h3
  have h4 := Submodule.finrank_le (Wt S g t ⊔ P ⊔ Pc)
  have h5 := finrank_range_le_map_add
    (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) (Wt S g t ⊔ P ⊔ Pc)
  have h6 := Submodule.finrank_mono hU
  change finrank (ZMod 2) (LinearMap.range
    (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) ≤ 4
  omega

theorem finrank_commSpace_le_four (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (F : Frame X)
    {k : S.M} (hkR : S.ρ k ∈ Rbar S g t) (hπk : act (F.π ⟨S.ρ k, hkR⟩) E00 ≠ E00)
    (hcP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g)) {x : S.O}
    (hxA : x ∈ S.Lbar g ⊓ Nbar S g t) (hxc : x ∈ S.Lbar ((k : G) * g)) :
    finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤ 4 := by
  obtain ⟨k', hk', -, hb'⟩ := X.exists_pair
  exact finrank_commSpace_le_four_of_fixW X F hkR hπk hcP hxA.1
    (fun w hw => (timmesfeld_10_1_two hCE X hk' hb').2.2.2.2 x hxA.2 w hw) hxc

end CFSG.LargeExtraspecial.S10
