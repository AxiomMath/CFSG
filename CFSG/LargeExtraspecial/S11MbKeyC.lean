module

public import CFSG.LargeExtraspecial.S11MbKeyB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G} {kb σ u₁ : G}

theorem YData.apply_sub_mem_clSub (Y : YData S g t τ u kb σ u₁) {x : G} (hxσ : x ∈ S.Qa u₁)
    (hxM : x ∈ S.M) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ centralizer ({σ} : Set G))) :
    (S.ρ ⟨x, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa u₁) := by
  obtain ⟨c, hc, hcQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hcσ : c * (u₁ * S.z * u₁⁻¹) = u₁ * S.z * u₁⁻¹ * c := by
    rw [← Y.conj_eq]
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
  rw [← S.cl_commutator hxM hcQ]
  have hQ : x * c * x⁻¹ * c⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG hxM hcQ) (S.QG.inv_mem hcQ)
  refine S.cl_mem_clSub (mem_inf.mpr ⟨hQ, ?_⟩) hQ
  rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
  exact mul_mem hxσ (conj_mem_Qa_of_commute' (inv_mem hxσ) hcσ)

theorem YData.commSpace_le_orthogonal (Y : YData S g t τ u kb σ u₁) :
    commSpace (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin
        (S.clSub (S.QG ⊓ centralizer ({σ} : Set G))) := by
  have hCfix : S.clSub (S.QG ⊓ centralizer ({σ} : Set G)) ≤
      fixSpace (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have := S.clSub_centralizer_le_fixQt Y.mem_M
    rwa [S.fixQt_of_mem Y.mem_M] at this
  rw [commSpace_eq_orthogonal_fixSpace_of_mem S.q_nondegenerate (S.ρ ⟨σ, Y.mem_M⟩).2]
  exact LinearMap.BilinForm.orthogonal_le hCfix

theorem YData.tau_b_facts (K : Conf S g t τ u) (Y : YData S g t τ u kb σ u₁)
    (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u) : ∃ h : (τ : G) * (kb * S.z * kb⁻¹) ∈ S.M,
    (τ : G) * (kb * S.z * kb⁻¹) ∈ S.Qa u₁ ∧ S.ρ ⟨(τ : G) * (kb * S.z * kb⁻¹), h⟩ = t := by
  have hbQ : kb * S.z * kb⁻¹ ∈ S.QG := (mem_inf.mp hb).1
  refine ⟨S.M.mul_mem τ.2 (S.QG_le_M hbQ), Y.tau_b_mem, ?_⟩
  have e : (⟨(τ : G) * (kb * S.z * kb⁻¹), S.M.mul_mem τ.2 (S.QG_le_M hbQ)⟩ : S.M) =
      τ * ⟨kb * S.z * kb⁻¹, S.QG_le_M hbQ⟩ := Subtype.ext rfl
  rw [e, map_mul, K.rho_eq, (S.ρ_eq_one_iff ⟨kb * S.z * kb⁻¹, S.QG_le_M hbQ⟩).mpr hbQ, mul_one]

variable (hy : Hyp S g) (K : Conf S g t τ u) (hm : finrank (ZMod 2) (Vt S g t) = 2)
  (Y : YData S g t τ u kb σ u₁)
  (hcase : ∀ w ∈ Wt S g t, (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
    (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
  (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u) (hCE : CentralExtInput.{u_G})
include hy K hm hcase hb

include hCE

theorem YData.clSub_le_commSpace :
    S.clSub (S.QG ⊓ S.Qa u₁) ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u₁)) = 2 := by
  have hF2 := Y.finrank_clSub_le_two hy K hm hcase
  have hdC := Y.finrank_clSub_centralizer hy K hm hcase
  obtain ⟨hτbM, hτbσ, hρ⟩ := Y.tau_b_facts K hb
  obtain ⟨w₀, hw₀, hq1, -⟩ := Y.exists_commSpace hy K hm hcase
  set C := S.clSub (S.QG ⊓ centralizer ({σ} : Set G)) with hC
  set F := S.clSub (S.QG ⊓ S.Qa u₁) with hF
  set D := F ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hD
  have hCD : C.map ((t : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤ D := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, sub_mem_commSpace _ _⟩
    have := Y.apply_sub_mem_clSub hτbσ hτbM hv
    rwa [hρ] at this
  have hD2 : 2 ≤ finrank (ZMod 2) D := by
    by_contra h1
    push Not at h1
    have h2 := Submodule.finrank_mono hCD
    have h3 := S2.finrank_map_sub_one_add (t : S.Qt ≃ₗ[ZMod 2] S.Qt) C
    have h4 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
    rw [K.timmesfeld_11_7 hy hCE] at h4
    have h5 := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
    have h6 := S.finrank_Qt_eq_two_mul_width
    have hfix : C ⊓ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
    have hle : LinearMap.BilinForm.orthogonal S.q.polarBilin C ≤
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [commSpace_eq_orthogonal_fixSpace_of_mem S.q_nondegenerate t.2]
      exact LinearMap.BilinForm.orthogonal_le (hfix ▸ inf_le_left)
    have := K.q_eq_zero hy (hle (Y.commSpace_le_orthogonal hw₀))
    rw [hq1] at this
    exact absurd this (by decide)
  have hDF' := Submodule.finrank_mono (inf_le_left : D ≤ F)
  rw [← hD] at hDF'
  have hDF : D = F := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  refine ⟨fun v hv => ?_, by rw [← hDF]; omega⟩
  rw [← hDF] at hv
  exact hv.2

omit hCE in
theorem YData.inf_Vt_le (hbs : S.cl (kb * S.z * kb⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    S.clSub (S.QG ⊓ S.Qa u₁) ⊓ Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  rintro v ⟨hvF, hvV⟩
  obtain ⟨f, hf, hfQ, rfl⟩ := S.mem_clSub_iff.mp hvF
  have hfσ : f ∈ S.Qa u₁ := (mem_inf.mp hf).2
  have haσ := Y.a_mem
  have haE := K.a_mem_E hy
  have hspan : ∀ x, x ∈ S.Qa u₁ → x = g * S.z * g⁻¹ * (kb * S.z * kb⁻¹) → False := by
    intro x hx hxe
    apply Y.b_not_mem
    have := mul_mem (inv_mem haσ) (hxe ▸ hx)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hez : ∀ e ∈ S.QG ⊓ S.Qa u, e ≠ 1 → f * S.z = e →
      S.cl e ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro e he he1 hfe
    obtain ⟨j, hj⟩ := K.exists_conj hy he he1
    have hez : e ≠ S.z := fun h => K.z_not_mem (h ▸ (mem_inf.mp he).2)
    obtain ⟨q, hq, hqe⟩ := S.exists_conj_eq_mul_z (mem_inf.mp he).1 he1 hez
    have hf' : (q * j) * S.z * (q * j)⁻¹ = f := by
      calc (q * j) * S.z * (q * j)⁻¹ = q * (j * S.z * j⁻¹) * q⁻¹ := by group
        _ = e * S.z := by rw [hj, hqe]
        _ = f := by rw [← hfe, mul_assoc, S.z_mul_z, mul_one]
    have := Y.cl_mem_span_of_conj hy K hm hcase (j := q * j) (by rw [hf']; exact hf)
    rwa [hf', ← S.cl_mul_z hfQ, hfe] at this
  rcases K.mem_V_cases hy (S.mem_clPre.mpr ⟨hfQ, hvV⟩) with hE | hE
  · rcases K.mem_E_cases hy hm hb hbs hE with h | h | h | h
    · rw [h, S.cl_one]
      exact zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _
    · exact absurd (h ▸ hfσ) Y.b_not_mem
    · exact (hspan f hfσ h).elim
  · rw [← S.cl_mul_z hfQ]
    by_cases h1 : f * S.z = 1
    · rw [h1, S.cl_one]
      exact zero_mem _
    exact hez _ hE h1 rfl

end CFSG.LargeExtraspecial.S11
