module

public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S3bNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

section Generic

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V} {q' : QuadraticForm (ZMod 2) V'}

theorem polar_map_of_isometry (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v) (x y : V) :
    polar q' (φ x) (φ y) = polar q x y := by
  rw [polar, polar, ← map_add, hφ, hφ, hφ]

theorem mem_pointRadical_of_intertwine (φ : V ≃ₗ[ZMod 2] V') (hφ : ∀ v, q' (φ v) = q v)
    {t : V ≃ₗ[ZMod 2] V} {t' : V' ≃ₗ[ZMod 2] V'} (ht : ∀ v, t' (φ v) = φ (t v)) {a : V}
    (h : t ∈ pointRadical q a) : t' ∈ pointRadical q' (φ a) := by
  obtain ⟨htO, hta, h1, h2⟩ := h
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (iso_of_intertwine φ hφ ht
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp htO)), by rw [ht, hta], fun x' hx' => ?_,
    fun v' => ?_⟩
  · obtain ⟨x, rfl⟩ := φ.surjective x'
    rw [polar_map_of_isometry φ hφ] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h1 x hx')
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [ht, ← map_sub, ← hc, map_smul]
  · obtain ⟨v, rfl⟩ := φ.surjective v'
    rw [ht, ← map_sub, polar_map_of_isometry φ hφ]
    exact h2 v

end Generic

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem exists_mem_pointRadical_of_fixLbar_ne (h2 : 2 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hfix : S.fixLbar g ≠ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    ∃ s ∈ S.Lbar g, s ≠ 1 ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  obtain ⟨v, hv, hva⟩ : ∃ v ∈ S.fixLbar g, v ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    by_contra h
    push Not at h
    exact hfix (le_antisymm h ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (S.cl_mem_fixLbar_self haQ)))
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  have hconj := (S.cl_mem_fixLbar_iff hxQ).mp hv
  have hxQa : x ∉ S.Qa g := by
    intro hxa
    apply hva
    have hfix' : ∀ y ∈ S.L0 g, S.cl (y * x * y⁻¹) = S.cl x := fun y hy => by
      rcases hconj y hy with h | h
      · rw [h]
      · rw [h, S.cl_mul_z hxQ]
    rcases S.mem_of_cl_fixed_by_L0 haQ hne ⟨hxQ, hxa⟩ hfix' with h | h | h | h
    · rw [h, S.cl_one]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _
    · rw [h, S.cl_z]
      exact Submodule.zero_mem _
    · rw [h, S.cl_mul S.z_mem_QG haQ, S.cl_z, zero_add]
      exact Submodule.mem_span_singleton_self _
  have hxa := S.commute_conj_z_of_cl_mem_fixLbar h2 haQ hne hxQ hv
  set T := S.conjBy g with hT
  have hTz : T.z = g * S.z * g⁻¹ := rfl
  have hxTM : x ∈ T.M := T.mem_M_iff.mpr (by rw [hTz]; exact hxa)
  have hzQa : S.z ∈ T.QG := S.z_mem_Qa haQ hne
  have hz0 : T.cl S.z ≠ 0 := fun h => by
    rcases (T.cl_eq_zero_iff hzQa).mp h with h' | h'
    · exact S.z_ne_one h'
    · exact hne h'.symm
  have hzq : T.q (T.cl S.z) = 0 := (T.q_cl_eq_zero_iff hzQa).mpr S.z_sq
  have hrad : (T.ρ ⟨x, hxTM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) ∈ pointRadical T.q (T.cl S.z) := by
    have hfz : (T.ρ ⟨x, hxTM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) (T.cl S.z) = T.cl S.z := by
      rw [T.ρ_cl _ hzQa]
      congr 1
      change x * S.z * x⁻¹ = S.z
      rw [S.z_comm (S.QG_le_M hxQ)]
      group
    refine ⟨(T.ρ ⟨x, hxTM⟩).2, hfz, fun w hw => ?_, fun w => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := T.exists_cl w
      have hyz : y * S.z = S.z * y := ((T.polar_cl_eq_zero_iff hzQa hy).mp hw).symm
      have hyL : y ∈ S.L0 g := ⟨hy, S.mem_M_iff.mpr hyz⟩
      rw [← T.cl_commutator hxTM hy]
      rcases S.conj_eq_or_of_conj_eq_or (S.QG_le_M hxQ) (S.L0_le_M g hyL) (hconj y hyL) with
        h | h
      · rw [show x * y * x⁻¹ * y⁻¹ = 1 by rw [h]; group, T.cl_one]
        exact Submodule.zero_mem _
      · rw [show x * y * x⁻¹ * y⁻¹ = y * S.z * y⁻¹ by rw [h], show y * S.z * y⁻¹ = S.z by
          rw [hyz]; group]
        exact Submodule.mem_span_singleton_self _
    · have h1 : polar T.q (T.cl S.z) ((T.ρ ⟨x, hxTM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) w) =
          polar T.q (T.cl S.z) w := by
        conv_lhs => rw [← hfz]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (T.ρ ⟨x, hxTM⟩).2 _ _
      rw [polar_sub_right, h1, sub_self]
  obtain ⟨u, -, huz, hua⟩ := S.exists_swap rfl haQ hne
  have hk : u * T.z * u⁻¹ = S.z := hua
  have hk' : u * S.z * u⁻¹ = T.z := huz
  have hxL : u * x * u⁻¹ ∈ S.L0 g :=
    ⟨conj_mem_QG_of_conj_eq S T hk' hxQ, conj_mem_M_of_conj_eq T S hk hxTM⟩
  have hxQ' : u * x * u⁻¹ ∉ S.QG := by
    intro hmem
    apply hxQa
    have := conj_mem_QG_of_conj_eq S T (inv_conj_eq_of_conj_eq T S hk) hmem
    exact (by simpa [mul_assoc] using this : x ∈ T.QG)
  have hrad' := mem_pointRadical_of_intertwine (transportQt T S hk) (q_transportQt T S hk)
    (transportQt_ρ T S hk ⟨x, hxTM⟩) hrad
  rw [transportQt_cl T S hk hzQa, hk'] at hrad'
  refine ⟨_, S.ρ_mem_Lbar hxL, fun h1 => hxQ' ((S.ρ_eq_one_iff _).mp h1), ?_⟩
  exact hrad'

theorem fixLbar_eq_span_of_pointRadical (h2 : 2 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (h : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1) :
    S.fixLbar g = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  by_contra hne'
  obtain ⟨s, hs, hs1, hsN⟩ := S.exists_mem_pointRadical_of_fixLbar_ne h2 haQ hne hne'
  exact hs1 (h s hs hsN)

end Setting

end CFSG.LargeExtraspecial
