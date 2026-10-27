module

public import CFSG.ClassicalGroups.Orthogonal.Transitive

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

attribute [local simp] HypPair.Q_e HypPair.Q_f HypPair.polar_ef HypPair.polar_fe
  HypPair.polar_ee HypPair.polar_ff

theorem commutatorElement_eichler {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u v : V} (hgu : g u = u)
    (hv : polar Q u v = 0) : ⁅g, eichler Q u v⁆ = eichler Q u (g v - v) := by
  have hgv : polar Q u (g v) = 0 := by
    rw [← polar_map_of_mem hg u v, hgu] at hv
    exact hv
  rw [commutatorElement_def, eichler_conj hg, hgu, eichler_inv hv,
    eichler_mul hgv (by rw [polar_neg_right, hv, neg_zero]), sub_eq_add_neg]

section Perfect

variable {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)

private theorem mk_commutatorElement_mem {a b : V ≃ₗ[K] V} (ha : a ∈ elementaryGroup Q)
    (hb : b ∈ elementaryGroup Q) (hab : ⁅a, b⁆ ∈ elementaryGroup Q) :
    (⟨⁅a, b⁆, hab⟩ : elementaryGroup Q) ∈ commutator (elementaryGroup Q) := by
  have : (⟨⁅a, b⁆, hab⟩ : elementaryGroup Q) = ⁅(⟨a, ha⟩ : elementaryGroup Q), ⟨b, hb⟩⁆ := rfl
  rw [this]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

include h₁₂ h₂₃ h₁₃ in
private theorem eichler_e₂_mem (t : K) :
    (⟨eichler Q P₁.e (t • P₂.e), eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  have hg := eichler_mem_orthogonalGroup Q P₃.e (t • P₂.e)
  have hgu : eichler Q P₃.e (t • P₂.e) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₃.ee]) (by rw [polar_smul_right_eq, h₁₂.ee,
      mul_zero])
  have hgf : eichler Q P₃.e (t • P₂.e) P₃.f - P₃.f = t • P₂.e := by
    rw [eichler_apply P₃.Q_e (by rw [polar_smul_right_eq, polar_comm, h₂₃.ee, mul_zero]),
      polar_smul_right_eq, polar_comm Q P₃.f P₂.e, h₂₃.ef, map_smul_eq_sq, P₂.Q_e, P₃.polar_fe]
    simp
  have h := commutatorElement_eichler hg hgu h₁₃.ef
  rw [hgf] at h
  have := mk_commutatorElement_mem (eichler_mem_elementaryGroup Q P₃.e (t • P₂.e))
    (eichler_mem_elementaryGroup Q P₁.e P₃.f) (by rw [h]; exact eichler_mem_elementaryGroup Q _ _)
  simpa only [h] using this

include h₁₂ h₂₃ h₁₃ in
private theorem eichler_f₂_mem (t : K) :
    (⟨eichler Q P₁.e (t • P₂.f), eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  have hg := eichler_mem_orthogonalGroup Q P₃.e (t • P₂.f)
  have hgu : eichler Q P₃.e (t • P₂.f) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₃.ee]) (by rw [polar_smul_right_eq, h₁₂.ef,
      mul_zero])
  have hgf : eichler Q P₃.e (t • P₂.f) P₃.f - P₃.f = t • P₂.f := by
    rw [eichler_apply P₃.Q_e (by rw [polar_smul_right_eq, polar_comm, h₂₃.fe, mul_zero]),
      polar_smul_right_eq, polar_comm Q P₃.f P₂.f, h₂₃.ff, map_smul_eq_sq, P₂.Q_f, P₃.polar_fe]
    simp
  have h := commutatorElement_eichler hg hgu h₁₃.ef
  rw [hgf] at h
  have := mk_commutatorElement_mem (eichler_mem_elementaryGroup Q P₃.e (t • P₂.f))
    (eichler_mem_elementaryGroup Q P₁.e P₃.f) (by rw [h]; exact eichler_mem_elementaryGroup Q _ _)
  simpa only [h] using this

include h₁₂ in
private theorem eichler_w_mem {w : V} (hw₁ : polar Q P₁.e w = 0) (hw₂ : polar Q P₂.e w = 0)
    (hw₂' : polar Q P₂.f w = 0) :
    (⟨eichler Q P₁.e (w - Q w • P₂.e), eichler_mem_elementaryGroup Q _ _⟩ :
      elementaryGroup Q) ∈ commutator (elementaryGroup Q) := by
  have hg := eichler_mem_orthogonalGroup Q P₂.e w
  have hgu : eichler Q P₂.e w P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₂.ee]) hw₁
  have hgf : eichler Q P₂.e w P₂.f - P₂.f = w - Q w • P₂.e := by
    rw [eichler_apply P₂.Q_e hw₂, hw₂', P₂.polar_fe]
    simp only [one_smul, zero_add, mul_one]
    abel
  have h := commutatorElement_eichler hg hgu h₁₂.ef
  rw [hgf] at h
  have := mk_commutatorElement_mem (eichler_mem_elementaryGroup Q P₂.e w)
    (eichler_mem_elementaryGroup Q P₁.e P₂.f) (by rw [h]; exact eichler_mem_elementaryGroup Q _ _)
  simpa only [h] using this

include h₁₂ h₁₃ h₂₃ in
theorem eichler_mem_commutator_of_center {v : V} (hv : polar Q P₁.e v = 0) :
    (⟨eichler Q P₁.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  set a := polar Q v P₂.f
  set b := polar Q v P₂.e
  set w := v - polar Q v P₁.f • P₁.e - a • P₂.e - b • P₂.f with hw
  have hw₁ : polar Q P₁.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, hv, P₁.polar_ee, h₁₂.ee, h₁₂.ef]
    ring
  have hw₂ : polar Q P₂.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, P₂.polar_ee, P₂.polar_ef, polar_comm Q P₂.e P₁.e,
      h₁₂.ee, polar_comm Q P₂.e v]
    ring
  have hw₂' : polar Q P₂.f w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, P₂.polar_ff, P₂.polar_fe, polar_comm Q P₂.f P₁.e,
      h₁₂.ef, polar_comm Q P₂.f v]
    ring
  have hdecomp : v = (a • P₂.e + b • P₂.f + w) + polar Q v P₁.f • P₁.e := by
    rw [hw]
    abel
  have he₂ : polar Q P₁.e ((a + Q w) • P₂.e) = 0 := by rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  have hf₂ : polar Q P₁.e (b • P₂.f) = 0 := by rw [polar_smul_right_eq, h₁₂.ef, mul_zero]
  have hw' : polar Q P₁.e (w - Q w • P₂.e) = 0 := by
    rw [polar_sub_right, polar_smul_right_eq, hw₁, h₁₂.ee, mul_zero, sub_zero]
  have hprod : eichler Q P₁.e v = eichler Q P₁.e ((a + Q w) • P₂.e) *
      eichler Q P₁.e (b • P₂.f) * eichler Q P₁.e (w - Q w • P₂.e) := by
    rw [eichler_mul he₂ hf₂, eichler_mul (by rw [polar_add_right, he₂, hf₂, add_zero]) hw',
      hdecomp, eichler_add_smul_self P₁.Q_e]
    congr 1
    rw [add_smul]
    abel
  have := mul_mem (mul_mem (eichler_e₂_mem h₁₂ h₁₃ h₂₃ (a + Q w)) (eichler_f₂_mem h₁₂ h₁₃ h₂₃ b))
    (eichler_w_mem h₁₂ hw₁ hw₂ hw₂')
  convert this using 1
  exact Subtype.ext hprod

include h₁₂ h₁₃ h₂₃ in
theorem commutator_elementaryGroup_eq_top (hQ : (polarBilin Q).Nondegenerate) :
    commutator (elementaryGroup Q) = ⊤ := by
  set N := commutator (elementaryGroup Q)
  have hN : N.Normal := inferInstance
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ P₁.e_ne_zero hu0
      (by rw [P₁.Q_e, hu])
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q P₁.e (g⁻¹ w) = 0 := by
      rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_inv_apply', hw]
    have hmem := hN.conj_mem _ (eichler_mem_commutator_of_center h₁₂ h₁₃ h₂₃ hv) ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q P₁.e (g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, LinearEquiv.apply_inv_apply']
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

end Perfect

end CFSG.ClassicalGroups.Orthogonal
