module

public import CFSG.ClassicalInvolution.SmallOrth.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_swap {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hwu' : polar Q w (-u) = 0 := by rw [polar_neg_right, hwu, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu', hw, QuadraticMap.map_neg, hu, polar_neg_right]
  simp only [zero_mul, add_zero, neg_smul, sub_neg_eq_add, smul_neg]
  abel

section Subgroup

variable (P : HypPair Q) (H : Subgroup (V ≃ₗ[K] V))

theorem exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H) (hW : ∃ g ∈ H, g P.e = P.f) {z : V}
    (hz : Q z = 0) (hez : polar Q P.e z ≠ 0) : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • z := by
  obtain ⟨g₀, hg₀, hg₀f⟩ := hW
  set b := polar Q P.e z with hb
  set z' := b⁻¹ • z with hz'
  have hz'1 : polar Q P.e z' = 1 := by rw [hz', polar_smul_right_eq, inv_mul_cancel₀ hez]
  have hQz' : Q z' = Q P.f := by
    rw [hz', map_smul_eq_sq, hz, P.Q_f, mul_zero]
  have hw : polar Q P.e ((1 : K)⁻¹ • (z' - P.f)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hz'1, P.polar_ef, sub_self, mul_zero]
  have h1 := eichler_apply_eq_of_polar_eq P.Q_e hQz'.symm P.polar_ef hz'1 one_ne_zero
  refine ⟨eichler Q P.e ((1 : K)⁻¹ • (z' - P.f)) * g₀, mul_mem (hU _ hw) hg₀, b⁻¹,
    inv_ne_zero hez, ?_⟩
  rw [LinearEquiv.mul_apply, hg₀f, h1]

variable {P}

theorem exists_mem_subgroup_apply_eq_smul (hQ : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H) (hW : ∃ g ∈ H, g P.e = P.f) {z : V}
    (hz : Q z = 0) (hz0 : z ≠ 0) : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • z := by
  by_cases hez : polar Q P.e z = 0
  swap
  · exact exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero P H hU hW hz hez
  by_cases hze : ∀ c : K, z ≠ c • P.e
  swap
  · push Not at hze
    obtain ⟨c, rfl⟩ := hze
    have hc : c ≠ 0 := by
      rintro rfl
      exact hz0 (zero_smul K P.e)
    refine ⟨1, one_mem _, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl
  obtain ⟨y, hy, hey, hyz⟩ := exists_singular_polar_ne_zero_both hQ P.Q_e P.e_ne_zero hez hze
  obtain ⟨g₁, hg₁, c₁, hc₁, h₁⟩ :=
    exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero P H hU hW hy hey
  have hg₁O := hH hg₁
  have hg₁'O := hH (inv_mem hg₁)
  have hQ₁ : Q (g₁⁻¹ z) = 0 := by rw [map_of_mem hg₁'O, hz]
  have hE₁ : polar Q P.e (g₁⁻¹ z) ≠ 0 := by
    rw [← polar_map_of_mem hg₁O P.e (g₁⁻¹ z), LinearEquiv.apply_inv_apply', h₁,
      polar_smul_left_eq]
    exact mul_ne_zero hc₁ hyz
  obtain ⟨g₂, hg₂, c₂, hc₂, h₂⟩ :=
    exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero P H hU hW hQ₁ hE₁
  refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, c₂, hc₂, ?_⟩
  rw [LinearEquiv.mul_apply, h₂, map_smul, LinearEquiv.apply_inv_apply']

theorem elementaryGroup_le_of_subgroup (hQ : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H) (hW : ∃ g ∈ H, g P.e = P.f) :
    elementaryGroup Q ≤ H := by
  apply elementaryGroup_le_of_eichler_mem
  intro u w hu hw
  by_cases hu0 : u = 0
  · subst hu0
    rw [eichler_zero_left]
    exact one_mem _
  obtain ⟨g, hg, c, hc, hgu⟩ := exists_mem_subgroup_apply_eq_smul H hQ hH hU hW hu hu0
  have hgO := hH hg
  have hv : polar Q P.e (c⁻¹ • g⁻¹ w) = 0 := by
    rw [polar_smul_right_eq, ← polar_map_of_mem hgO P.e (g⁻¹ w), hgu,
      LinearEquiv.apply_inv_apply', polar_smul_left_eq, hw, mul_zero, mul_zero]
  have h1 : eichler Q u w = g * eichler Q P.e (c⁻¹ • g⁻¹ w) * g⁻¹ := by
    rw [eichler_conj hgO, hgu, map_smul, LinearEquiv.apply_inv_apply', eichler_smul_left,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [h1]
  exact mul_mem (mul_mem hg (hU _ hv)) (inv_mem hg)

end Subgroup

end CFSG.ClassicalGroups.Orthogonal.Small
