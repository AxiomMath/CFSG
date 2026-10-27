module

public import CFSG.LargeExtraspecial.S4FiveMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def orbV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g)
    {f : S.O} (hf : f ∈ Rbar S g t) : Vt S g t :=
  resV haQ t ⟨f, hf⟩ (aV ht)

theorem coe_orbV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) {f : S.O}
    (hf : f ∈ Rbar S g t) :
    (orbV haQ ht hf : S.Qt) = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
  rfl

theorem exists_Lbar_of_mem_LmodN {t : S.O} {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t}
    (he : e ∈ LmodN S g t) : ∃ l ∈ S.Lbar g, ∀ v : Vt S g t,
      ((e v : Vt S g t) : S.Qt) = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  he

theorem exists_move_of {f₁ f₂ l : S.O} (hl : l ∈ S.Lbar g)
    (hlc : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (((f₁⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))) =
        ((f₁⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (S.cl (g * S.z * g⁻¹))) + S.cl (g * S.z * g⁻¹)) :
    ∃ y ∈ (S.Lbar g).map (MulAut.conj f₁).toMonoidHom,
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  refine ⟨f₁ * l * f₁⁻¹, ⟨l, hl, rfl⟩, ?_⟩
  rw [coe_mul_apply, coe_mul_apply, hlc, map_add, apply_inv_apply_O]

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {F : Subgroup S.O}
  (hFR : F ≤ Rbar S g t)
include H ht hFR

theorem orbV_ne_aV {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hne : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) :
    orbV H.conj_mem ht (hFR (mul_mem (inv_mem hf₁) hf₂)) ∉ (ZMod 2) ∙ aV ht := by
  intro hmem
  rw [mem_span_singleton_subtype, coe_orbV, mem_span_cl_iff, coe_mul_apply] at hmem
  rcases hmem with h0 | h1
  · have := congrArg (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
    rw [apply_inv_apply_O, map_zero] at this
    have h3 := congrArg ((f₂⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) this
    rw [inv_apply_apply_O, map_zero] at h3
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne h3
  · apply hne
    have := congrArg (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rw [apply_inv_apply_O] at this
    exact this.symm

theorem exists_move_lin (hL : LinCase S g ht) {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hne : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) :
    ∃ y ∈ (S.Lbar g).map (MulAut.conj f₁).toMonoidHom,
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  have hc := orbV_ne_aV H ht hFR hf₁ hf₂ hne
  obtain ⟨φ, hφc, hφa⟩ := Submodule.exists_le_ker_of_notMem hc
  have hφa' : φ (aV ht) = 0 := hφa (Submodule.mem_span_singleton_self _)
  have hφ1 := zmod2_eq_one_of_ne_zero hφc
  have he : LinearEquiv.transvection hφa' ∈ LmodN S g t := by
    rw [hL.LmodN_eq]
    exact transvection_mem_centreGroup hφa'
  obtain ⟨l, hl, hle⟩ := exists_Lbar_of_mem_LmodN he
  refine exists_move_of hl ?_
  have := hle (orbV H.conj_mem ht (hFR (mul_mem (inv_mem hf₁) hf₂)))
  rw [LinearEquiv.transvection.apply, hφ1, one_smul, Submodule.coe_add, coe_orbV,
    coe_mul_apply] at this
  exact this.symm

theorem act_lin (hL : LinCase S g ht) {l : S.O} (hl : l ∈ S.Lbar g) {u : S.Qt}
    (hu : u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  have huV : u ∈ Vt S g t := by
    refine (Submodule.span_le.mpr ?_) hu
    rintro _ ⟨f, hf, rfl⟩
    exact apply_mem_Vt_of_mem_Rbar H.conj_mem (hFR hf) (cl_a_mem_Vt ht)
  have he : resL H.conj_mem ht ⟨l, hl⟩ ∈ centreGroup (Vt S g t) (aV ht) := by
    rw [← hL.LmodN_eq, ← range_resL H.conj_mem ht]
    exact ⟨_, rfl⟩
  have := he ⟨u, huV⟩
  rw [mem_span_singleton_subtype] at this
  exact this

variable (C : Cons311 S g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
include C ht1 hVQ

theorem beta_aV_orbV_mul {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) :
    beta H C ht ht1 hVQ (aV ht) (orbV H.conj_mem ht (hFR (mul_mem (inv_mem hf₁) hf₂))) =
      beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) := by
  have e2 : resV H.conj_mem t ⟨f₁, hFR hf₁⟩
      (orbV H.conj_mem ht (hFR (mul_mem (inv_mem hf₁) hf₂))) = orbV H.conj_mem ht (hFR hf₂) :=
    Subtype.ext (by rw [coe_resV_apply, coe_orbV, coe_orbV, coe_mul_apply, apply_inv_apply_O])
  rw [← beta_apply_resV H C ht ht1 hVQ ⟨f₁, hFR hf₁⟩, e2]
  rfl

theorem exists_move_perp
    (hτ : LmodN S g t = spPointRadical (beta H C ht ht1 hVQ) (aV ht) ∨
      spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t)
    {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hne : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))
    (hperp : beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁))
      (orbV H.conj_mem ht (hFR hf₂)) = 0) :
    ∃ y ∈ (S.Lbar g).map (MulAut.conj f₁).toMonoidHom,
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
        (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hβ := beta_isAlt H C ht ht1 hVQ
  set c := orbV H.conj_mem ht (hFR (mul_mem (inv_mem hf₁) hf₂)) with hcdef
  have hc := orbV_ne_aV H ht hFR hf₁ hf₂ hne
  have hac : beta H C ht ht1 hVQ (aV ht) c = 0 := by
    rw [hcdef, beta_aV_orbV_mul H ht hFR C ht1 hVQ hf₁ hf₂, hperp]
  have hca : beta H C ht ht1 hVQ c (aV ht) = 0 := by rw [isAlt_symm hβ, hac]
  obtain ⟨d, had, -, hcd⟩ := exists_dual_triple hβ (beta_nondegenerate H C ht ht1 hVQ)
    (b := aV ht) (c := aV ht) (e := c) (by rwa [Set.pair_eq_singleton])
  have hρ : spRho hβ had 0 c = c + aV ht := by
    rw [spRho_apply, hca, zero_smul, add_zero, hcd, mul_zero, add_zero, one_smul]
  obtain ⟨e, he, hec⟩ : ∃ e ∈ LmodN S g t, e c = c + aV ht := by
    rcases hτ with hU | hτ
    · exact ⟨_, hU ▸ spRho_mem_spPointRadical hβ had 0, hρ⟩
    · rcases mem_or_mul_mem_of_card (LmodN_le_spPointRadical H C ht ht1 hVQ)
          (card_spPointRadical_le_two_mul H C ht ht1 hVQ) (spTransvection_mem_U hβ _) hτ
          (spRho_mem_spPointRadical hβ had 0) with h | h
      · exact ⟨_, h, hρ⟩
      · refine ⟨_, h, ?_⟩
        rw [LinearEquiv.mul_apply, spTransvection_apply, hca, zero_smul, add_zero, hρ]
  obtain ⟨l, hl, hle⟩ := exists_Lbar_of_mem_LmodN he
  refine exists_move_of hl ?_
  have := hle c
  rw [hec, Submodule.coe_add, hcdef, coe_orbV, coe_mul_apply] at this
  exact this.symm

theorem act_perp
    (hperp : ∀ f (hf : f ∈ F), beta H C ht ht1 hVQ (aV ht) (orbV H.conj_mem ht (hFR hf)) = 0)
    {l : S.O} (hl : l ∈ S.Lbar g) {u : S.Qt}
    (hu : u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  set W : Submodule (ZMod 2) S.Qt :=
    (LinearMap.ker (beta H C ht ht1 hVQ (aV ht))).map (Vt S g t).subtype with hW
  have hle : Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨orbV H.conj_mem ht (hFR hf), LinearMap.mem_ker.mpr (hperp f hf), rfl⟩
  obtain ⟨x, hx, rfl⟩ := hle hu
  have hU := LmodN_le_spPointRadical H C ht ht1 hVQ
    ((range_resL H.conj_mem ht) ▸ ⟨⟨l, hl⟩, rfl⟩ : resL H.conj_mem ht ⟨l, hl⟩ ∈ LmodN S g t)
  have := hU.2.2.1 x (LinearMap.mem_ker.mp hx)
  rw [mem_span_singleton_subtype] at this
  exact this

end CFSG.LargeExtraspecial.S4
