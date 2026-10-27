module

public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem s12_polar_Lbar_apply {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {ℓ : S.O}
    (hℓ : ℓ ∈ S.Lbar g) {v : S.Qt} (hv : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) :
    polar S.q (S.cl (g * S.z * g⁻¹)) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0 := by
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ℓ.2
    (S.cl (g * S.z * g⁻¹)) v
  rw [S.s12_Lbar_apply_cl_a haQ hℓ] at h
  rw [h, hv]

theorem s12_isTypeA_apply_of_mem_commSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) {t : V ≃ₗ[ZMod 2] V} (ht : IsTypeA q t 2) {p : V}
    (hp : p ∈ commSpace t) (hp0 : p ≠ 0) :
    ∃ u : V, q u = 0 ∧ polar q p u = 0 ∧ commSpace t = Submodule.span (ZMod 2) {p, u} ∧
      ∀ v, polar q v p = 0 → t v = v + polar q v u • p := by
  obtain ⟨u, hli, hspan⟩ := OrthoF2.exists_pair_of_mem_of_finrank_eq_two ht.2.2.2.1 hp hp0
  obtain ⟨hqp, hqu, hpu, rfl⟩ := OrthoF2.eq_eichler_of_isTypeA hq ht hli hspan.symm
  refine ⟨u, hqu, hpu, hspan.symm, fun v hv => ?_⟩
  rw [eichler_apply_zmod2 hqp hpu, hv, zero_smul, add_zero, mul_zero, add_zero]

omit [Finite G] in
theorem s12_cl_conj_eq_mul {g x y : G} (hxQ : x ∈ S.QG) (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (h : y * x * y⁻¹ = g * S.z * g⁻¹ * x) :
    S.cl (y * x * y⁻¹) = S.cl (g * S.z * g⁻¹) + S.cl x := by
  rw [h, S.cl_mul haQ hxQ]

theorem timmesfeld_12_6 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.cl (g * S.z * g⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      ∃ u : S.Qt, S.q u = 0 ∧ polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 ∧
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
          Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹), u} ∧
        (∀ v, polar S.q v (S.cl (g * S.z * g⁻¹)) = 0 →
          (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar S.q v u • S.cl (g * S.z * g⁻¹)) ∧
        ∃ v, polar S.q v (S.cl (g * S.z * g⁻¹)) = 0 ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
  set a := g * S.z * g⁻¹ with ha
  set ã := S.cl a with hã
  have ha0 : ã ≠ 0 := S.s12_cl_ne_zero_of_conj haQ hne
  have hqa : S.q ã = 0 := (S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)
  have hnt : ∃ v, polar S.q ã v = 0 ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
    by_contra hc
    push Not at hc
    exact htA.2.1 (eq_one_of_fix_orthogonal_of_map_eq_zero S.q_nondegenerate hqa t.2 hc)
  set U : Submodule (ZMod 2) S.Qt :=
    (LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ ã)).map
      ((t : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hU
  have hmemU : ∀ v, polar S.q ã v = 0 → (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ U := by
    intro v hv
    refine ⟨v, ?_, rfl⟩
    exact OrthoF2.mem_orthogonal_span_singleton_iff.mpr hv
  have hUmem : ∀ w ∈ U, ∃ v, polar S.q ã v = 0 ∧ w = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, OrthoF2.mem_orthogonal_span_singleton_iff.mp hv, rfl⟩
  have hUinv : ∀ ℓ ∈ S.Lbar g, ∀ w ∈ U, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ U := by
    intro ℓ hℓ w hw
    obtain ⟨v, hv, rfl⟩ := hUmem w hw
    have hcomm : ℓ * t = t * ℓ :=
      congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨ℓ, hℓ⟩ ⟨t, ht⟩)
    have e : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
          (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      rw [map_sub]
      congr 1
      have := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hcomm
      simpa using this
    rw [e]
    exact hmemU _ (S.s12_polar_Lbar_apply haQ hℓ hv)
  have haU : ã ∈ U := by
    obtain ⟨v, hv, hv1⟩ := hnt
    have hw := hmemU v hv
    set w := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v with hw'
    have hw0 : w ≠ 0 := sub_ne_zero.mpr hv1
    by_cases hwa : w = ã
    · rw [← hwa]
      exact hw
    · have hwW : w ∈ S.clSub (S.QG ⊓ S.Qa g) := S.s12_Lbar_apply_sub_mem haQ ht hv
      obtain ⟨x, hxX, hxQ, hxw⟩ := S.mem_clSub_iff.mp hwW
      obtain ⟨-, y, hy, hyx⟩ := S.conj_L0_of_mem_QG_inf_Qa haQ hne hxX
        ⟨by rw [hxw]; exact hw0, by rw [hxw]; exact hwa⟩
      have hℓ : S.ρ ⟨y, S.L0_le_M g hy⟩ ∈ S.Lbar g := S.s12_mem_Lbar.mpr ⟨y, hy, rfl⟩
      have h1 := hUinv _ hℓ w hw
      rw [← hxw, S.ρ_cl _ hxQ] at h1
      change S.cl (y * x * y⁻¹) ∈ U at h1
      rw [S.s12_cl_conj_eq_mul hxQ haQ hyx] at h1
      have h2 : S.cl x ∈ U := hxw ▸ hw
      have := U.sub_mem h1 h2
      rwa [add_sub_cancel_right] at this
  have haC : ã ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    obtain ⟨v, -, hv⟩ := hUmem ã haU
    rw [hv]
    exact sub_mem_commSpace _ v
  obtain ⟨u, hqu, hau, hspan, happ⟩ :=
    s12_isTypeA_apply_of_mem_commSpace S.q_nondegenerate htA haC ha0
  refine ⟨haC, u, hqu, hau, hspan, happ, ?_⟩
  obtain ⟨v, hv, hv1⟩ := hnt
  exact ⟨v, by rw [QuadraticMap.polar_comm]; exact hv, hv1⟩

end Setting

end CFSG.LargeExtraspecial
