module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_of_mem_rootGroup_of_apply_eq {u u' : V} (hu : Q u = 0) (huu' : polar Q u u' ≠ 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ rootGroup Q u) (hgu' : g u' = u') : g = 1 := by
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  have hfix := hgu'
  rw [eichler_apply hu hw, add_sub_assoc, add_eq_left, sub_eq_zero] at hfix
  have hp : polar Q u' u ≠ 0 := by rwa [polar_comm]
  have hw_eq : w = ((polar Q u' u)⁻¹ * (polar Q u' w + Q w * polar Q u' u)) • u := by
    rw [mul_smul, ← hfix, smul_smul, inv_mul_cancel₀ hp, one_smul]
  rw [hw_eq, ← zero_add (_ • u), eichler_add_smul_self hu, eichler_zero_right]

theorem rootGroup_inf_eq_bot {u u' : V} (hu : Q u = 0) (huu' : polar Q u u' ≠ 0) :
    rootGroup Q u ⊓ rootGroup Q u' = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg₁, hg₂⟩
  obtain ⟨w', -, hg⟩ := mem_rootGroup.mp hg₂
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_rootGroup_of_apply_eq hu huu' hg₁
    (by rw [← hg]; exact eichler_apply_self u' w')

theorem rootGroup_sup_eq_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {u u' : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) :
    rootGroup Q u ⊔ rootGroup Q u' = elementaryGroup Q := by
  have hle : rootGroup Q u ⊔ rootGroup Q u' ≤ elementaryGroup Q :=
    sup_le (rootGroup_le_elementaryGroup Q u) (rootGroup_le_elementaryGroup Q u')
  refine le_antisymm hle ?_
  have hH := hle.trans (elementaryGroup_le_orthogonalGroup Q)
  have h1 : polar Q u ((polar Q u u')⁻¹ • u') = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ huu']
  let P : HypPair Q :=
    ⟨u, (polar Q u u')⁻¹ • u', hu, by rw [map_smul_eq_sq, hu', mul_zero], h1⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact huu' (polar_zero_left Q u')
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (polar_zero_right Q u)
  have he : IsRootCenter Q (rootGroup Q u ⊔ rootGroup Q u') u :=
    ⟨hu0, hu, fun w hw => le_sup_left (a := rootGroup Q u) (eichler_mem_rootGroup hw)⟩
  have hf : IsRootCenter Q (rootGroup Q u ⊔ rootGroup Q u') u' :=
    ⟨hu'0, hu', fun w hw => le_sup_right (b := rootGroup Q u') (eichler_mem_rootGroup hw)⟩
  exact elementaryGroup_le_of_hypPair hQ hH P he (hf.smul (inv_ne_zero huu'))

theorem polar_eichler_apply_left {u u' w : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (hw : polar Q u' w = 0) :
    polar Q u (eichler Q u' w u) = -(Q w * polar Q u u' ^ 2) := by
  rw [eichler_apply hu' hw, polar_sub_right, polar_add_right, polar_smul_right_eq,
    polar_smul_right_eq, polar_self_eq_zero hu]
  ring

theorem rootGroup_sup_zpowers_eichler (hQ : (polarBilin Q).Nondegenerate) {u u' w : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) (hw : polar Q u' w = 0)
    (hQw : Q w ≠ 0) :
    rootGroup Q u ⊔ Subgroup.zpowers (eichler Q u' w) = elementaryGroup Q := by
  set x := eichler Q u' w with hx
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q u' w
  refine le_antisymm (sup_le (rootGroup_le_elementaryGroup Q u)
    (Subgroup.zpowers_le.mpr (eichler_mem_elementaryGroup Q u' w))) ?_
  have hxu : Q (x u) = 0 := by rw [map_of_mem hxO, hu]
  have hp : polar Q u (x u) ≠ 0 := by
    rw [hx, polar_eichler_apply_left hu hu' hw]
    exact neg_ne_zero.mpr (mul_ne_zero hQw (pow_ne_zero 2 huu'))
  rw [← rootGroup_sup_eq_elementaryGroup hQ hu hxu hp]
  refine sup_le le_sup_left fun y hy => ?_
  have h1 : x⁻¹ * y * x⁻¹⁻¹ ∈ rootGroup Q (x⁻¹ (x u)) := conj_mem_rootGroup (inv_mem hxO) hy
  rw [inv_inv, LinearEquiv.inv_apply_apply'] at h1
  have hxX : x ∈ rootGroup Q u ⊔ Subgroup.zpowers x :=
    le_sup_right (a := rootGroup Q u) (b := Subgroup.zpowers x) (Subgroup.mem_zpowers x)
  have hy' : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [hy']
  exact mul_mem (mul_mem hxX (le_sup_left (b := Subgroup.zpowers x) h1)) (inv_mem hxX)

theorem exists_mem_rootGroup_mul_eq {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgu : g u = u) :
    ∃ s ∈ rootGroup Q u, ∃ h ∈ TauCeti.QuadraticMap.orthogonalGroup Q, h u = u ∧ h u' = u' ∧
      g = s * h := by
  have hQ : Q u' = Q (g u') := by rw [map_of_mem hg]
  have hp : polar Q u (g u') = polar Q u u' := by
    have h := polar_map_of_mem hg u u'
    rwa [hgu] at h
  have hw : polar Q u ((polar Q u u')⁻¹ • (g u' - u')) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hp, sub_self, mul_zero]
  set s := eichler Q u ((polar Q u u')⁻¹ • (g u' - u')) with hs
  have hsu' : s u' = g u' := eichler_apply_eq_of_polar_eq hu hQ rfl hp huu'
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q _ _
  have hsu : s u = u := eichler_apply_self u _
  refine ⟨s, eichler_mem_rootGroup hw, s⁻¹ * g, mul_mem (inv_mem hsO) hg, ?_, ?_, by group⟩
  · rw [LinearEquiv.mul_apply, hgu]
    conv_lhs => rw [← hsu]
    exact LinearEquiv.inv_apply_apply' s u
  · rw [LinearEquiv.mul_apply, ← hsu']
    exact LinearEquiv.inv_apply_apply' s u'

end CFSG.ClassicalGroups.Orthogonal
