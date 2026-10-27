module

public import CFSG.LargeExtraspecial.S3bEleven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem mem_pointRadical_of_width_eq_three (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 3) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  obtain ⟨-, -, hWts, hWn, hC⟩ :=
    (S.lemma_3_11_two hTI (by omega) haQ hne hno).resolve_left hirr
  set W := S.clSub (S.QG ⊓ S.Qa g) with hW
  set a' := S.cl (g * S.z * g⁻¹) with ha'
  set t := (s : S.Qt ≃ₗ[ZMod 2] S.Qt) with ht
  have ha0 : a' ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have haq : S.q a' = 0 := S.q_cl_conj_z haQ
  have hsa : t a' = a' := S.mem_fixLbar.mp (S.cl_mem_fixLbar_self haQ) s hs
  have htO : t ∈ S.O := s.2
  have htt : t * t = 1 := by
    have := S.sq_eq_one_of_mem_Lbar haQ hs
    rw [pow_two] at this
    rw [ht, ← Subgroup.coe_mul, this]
    rfl
  have hiso : ∀ v, S.q (t v) = S.q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp htO
  refine ⟨htO, hsa, fun x hx => ?_, fun v => ?_⟩
  swap
  · have h1 : polar S.q a' (t v) = polar S.q a' v := by
      conv_lhs => rw [← hsa]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO _ _
    rw [polar_sub_right, h1, sub_self]
  have hDW : ∀ v, polar S.q a' v = 0 → t v - v ∈ W := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := S.exists_cl v
    have hwa : w * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * w :=
      ((S.polar_cl_eq_zero_iff haQ hw).mp hv).symm
    exact S.sub_mem_clSub_of_mem_Lbar haQ hne hs hw hwa
  have hDfix : ∀ v, t (t v - v) = t v - v := by
    intro v
    have h1 : t (t v) = v := by
      rw [← LinearEquiv.mul_apply, htt]
      rfl
    rw [map_sub, h1, vec_sub, vec_sub, add_comm]
  have hDpolar : ∀ v, polar S.q a' v = 0 → polar S.q v (t v - v) = 0 := by
    intro v hv
    have h1 := hiso v
    rw [show t v = v + (t v - v) by abel, map_add_eq, hWts _ (hDW v hv), add_zero] at h1
    simpa using h1
  by_cases hs1 : s = 1
  · rw [ht, hs1]
    simp
  set K := W ⊓ fixSpace t with hK
  have hKlt : K < W := by
    refine lt_of_le_of_ne inf_le_left fun hKW => hs1 (hC s hs fun w hw => ?_)
    have : w ∈ K := hKW ▸ hw
    exact mem_fixSpace.mp this.2
  have hKdim : finrank (ZMod 2) K ≤ 2 := by
    have := Submodule.finrank_lt_finrank_of_lt hKlt
    omega
  have haK : a' ∈ K := ⟨S.cl_mem_clSub ⟨haQ, S.conj_z_mem_Qa g⟩ haQ, mem_fixSpace.mpr hsa⟩
  by_contra hxD
  set k := t x - x with hk
  have hkK : k ∈ K := ⟨hDW x hx, mem_fixSpace.mpr (hDfix x)⟩
  have hk0 : k ≠ 0 := by
    intro h
    apply hxD
    rw [h]
    exact Submodule.zero_mem _
  have hak : a' ≠ k := by
    intro h
    apply hxD
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  have hli : LinearIndependent (ZMod 2) ![a', k] :=
    linearIndependent_pair_iff.mpr ⟨ha0, hk0, hak⟩
  have hKeq : K = Submodule.span (ZMod 2) {a', k} := by
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact haK
      · exact hkK
    · rw [finrank_span_pair hli]
      exact hKdim
  obtain ⟨x', hx', hx'k⟩ : ∃ x', polar S.q a' x' = 0 ∧ polar S.q x' k = 1 := by
    by_contra h
    push Not at h
    apply hxD
    have hk' : k ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
        (LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ a')) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      rw [polarBilin_apply_apply]
      exact (zmod2_eq_zero_or_eq_one _).resolve_right
        (h y ((mem_orthogonal_span_singleton_iff).mp hy))
    rwa [LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl] at hk'
  have hxk : polar S.q x k = 0 := hDpolar x hx
  have hDx' : t x' - x' ∈ K := ⟨hDW x' hx', mem_fixSpace.mpr (hDfix x')⟩
  rw [hKeq] at hDx'
  obtain ⟨β, γ, hβγ⟩ := Submodule.mem_span_pair.mp hDx'
  have hβ : γ = 0 := by
    have h1 := hDpolar x' hx'
    rw [← hβγ, polar_add_right, polar_smul_right, polar_smul_right, polar_comm S.q x' a', hx',
      hx'k] at h1
    simpa using h1
  have hsum : polar S.q a' (x + x') = 0 := by rw [polar_add_right, hx, hx', add_zero]
  have h2 := hDpolar (x + x') hsum
  have e : t (x + x') - (x + x') = k + β • a' := by
    rw [map_add, show t x + t x' - (x + x') = (t x - x) + (t x' - x') by abel, ← hβγ, hβ,
      zero_smul, add_zero]
  rw [e, polar_add_right, polar_smul_right, polar_add_left, polar_add_left, hxk, hx'k,
    polar_comm S.q x a', polar_comm S.q x' a', hx, hx'] at h2
  simp at h2

theorem isTypeC_of_mem_Lbar_of_width_eq_three (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 3) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) {s : S.O} (hs : s ∈ S.Lbar g)
    (hs1 : s ≠ 1) : IsTypeC S.q (s : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  have hsN := S.mem_pointRadical_of_width_eq_three hTI hn haQ hne hno hirr hs
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  obtain ⟨u, hau, hsu⟩ := (mem_pointRadical_iff S.q_nondegenerate ha0 haq).mp hsN
  have hu : u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro hu
    apply hs1
    refine Subtype.ext ?_
    rw [hsu, (eichler_eq_one_iff S.q_nondegenerate ha0 haq hau).mpr hu]
    rfl
  have htypes := eichler_type_of_not_mem_span S.q_nondegenerate ha0 haq hau hu
  rcases zmod2_eq_zero_or_eq_one (S.q u) with h | h
  · exfalso
    obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
    have hyQ : (y : G) ∉ S.QG := fun h' => hs1 ((S.ρ_eq_one_iff y).mpr h')
    have hA := htypes.2.1 h
    rw [← hsu] at hA
    exact hno (S.hasTypeAInL_of_mem_L0 hy hyQ hA)
  · rw [hsu]
    exact htypes.2.2 h

end Setting

end CFSG.LargeExtraspecial
