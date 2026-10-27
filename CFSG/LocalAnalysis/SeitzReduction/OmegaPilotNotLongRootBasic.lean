module

public import CFSG.ClassicalGroups.Orthogonal.Perfect

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def rootPairSub (Q : QuadraticForm K V) (u u' : V) : Subgroup (V ≃ₗ[K] V) :=
  rootGroup Q u ⊔ rootGroup Q u'

theorem rootPairSub_comm (u u' : V) : rootPairSub Q u u' = rootPairSub Q u' u :=
  sup_comm _ _

theorem rootGroup_le_rootPairSub_left (u u' : V) : rootGroup Q u ≤ rootPairSub Q u u' :=
  le_sup_left

theorem rootGroup_le_rootPairSub_right (u u' : V) : rootGroup Q u' ≤ rootPairSub Q u u' :=
  le_sup_right

theorem eichler_eq_eichler_neg {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) : eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hw, QuadraticMap.map_neg, hu, polar_neg_right]
  module

theorem rootPairSub_le_centralizer {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' = 0) : rootPairSub Q u u' ≤ centralizer {eichler Q u u'} := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [mem_centralizer_singleton_iff]
    exact (rootGroup_commute (eichler_mem_rootGroup huu') hg).symm
  · rw [mem_centralizer_singleton_iff, eichler_eq_eichler_neg hu hu' huu']
    have h : polar Q u' (-u) = 0 := by rw [polar_neg_right, polar_comm, huu', neg_zero]
    exact (rootGroup_commute (eichler_mem_rootGroup h) hg).symm

theorem eichler_mem_rootPairSub {u u' : V} (huu' : polar Q u u' = 0) :
    eichler Q u u' ∈ rootPairSub Q u u' :=
  rootGroup_le_rootPairSub_left u u' (eichler_mem_rootGroup huu')

section Action

variable {P P' : HypPair Q} (h : P.Orth P')

include h

theorem polar_e_smul_f (t : K) : polar Q P.e (t • P'.f) = 0 := by
  rw [polar_smul_right_eq, h.ef, mul_zero]

omit h in
theorem eichler_smul_f_apply_e (t : K) : eichler Q P.e (t • P'.f) P.e = P.e :=
  eichler_apply_self _ _

theorem eichler_smul_f_apply_e' (t : K) :
    eichler Q P.e (t • P'.f) P'.e = P'.e - t • P.e := by
  rw [eichler_apply P.Q_e (polar_e_smul_f h t), polar_smul_right_eq, P'.polar_ef,
    polar_comm Q P'.e P.e, h.ee, map_smul_eq_sq, P'.Q_f]
  module

theorem eichler_smul_f_apply_f (t : K) :
    eichler Q P.e (t • P'.f) P.f = P.f + t • P'.f := by
  rw [eichler_apply P.Q_e (polar_e_smul_f h t), polar_smul_right_eq, P.polar_fe, h.ff,
    map_smul_eq_sq, P'.Q_f]
  module

theorem eichler_smul_f_apply_f' (t : K) : eichler Q P.e (t • P'.f) P'.f = P'.f := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm]; exact h.ef
  · rw [polar_smul_right_eq, P'.polar_ff, mul_zero]

end Action

section Perfect

variable {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)

theorem commutatorElement_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ ⁅H, H⁆ :=
  Subgroup.commutator_mem_commutator ha hb

include h₁₂ h₁₃ h₂₃ in
theorem eichler_smul_e_mem_commutator (c : K) :
    eichler Q P₁.e (c • P₂.e) ∈
      ⁅rootPairSub Q P₁.e P₂.e, rootPairSub Q P₁.e P₂.e⁆ := by
  have hw : polar Q P₂.e (-c • P₃.f) = 0 := by rw [polar_smul_right_eq, h₂₃.ef, mul_zero]
  have hg := eichler_mem_orthogonalGroup Q P₂.e (-c • P₃.f)
  have hgu : eichler Q P₂.e (-c • P₃.f) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero h₁₂.ee (by rw [polar_smul_right_eq, h₁₃.ef, mul_zero])
  have h := commutatorElement_eichler hg hgu h₁₃.ee
  have hv : eichler Q P₂.e (-c • P₃.f) P₃.e - P₃.e = c • P₂.e := by
    rw [eichler_apply P₂.Q_e hw, polar_comm Q P₃.e P₂.e, h₂₃.ee, polar_smul_right_eq,
      P₃.polar_ef]
    module
  rw [hv] at h
  rw [← h]
  exact commutatorElement_mem_commutator
    (rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup hw))
    (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup h₁₃.ee))

include h₁₂ in
theorem eichler_sub_mem_commutator {w : V} (hw₁ : polar Q P₁.e w = 0)
    (hw₂ : polar Q P₂.e w = 0) (hw₂' : polar Q P₂.f w = 0) :
    eichler Q P₁.e (w - Q w • P₂.e) ∈
      ⁅rootPairSub Q P₁.e P₂.e, rootPairSub Q P₁.e P₂.e⁆ := by
  have hg := eichler_mem_orthogonalGroup Q P₂.e w
  have hgu : eichler Q P₂.e w P₁.e = P₁.e := eichler_apply_of_polar_eq_zero h₁₂.ee hw₁
  have h := commutatorElement_eichler hg hgu h₁₂.ef
  have hv : eichler Q P₂.e w P₂.f - P₂.f = w - Q w • P₂.e := by
    rw [eichler_apply P₂.Q_e hw₂, hw₂', P₂.polar_fe]
    module
  rw [hv] at h
  rw [← h]
  exact commutatorElement_mem_commutator
    (rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup hw₂))
    (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup h₁₂.ef))

@[expose] noncomputable def torusWord (P₁ P₂ : HypPair Q) (l : K) : V ≃ₗ[K] V :=
  eichler Q P₂.e (-l⁻¹ • P₁.f) * eichler Q P₁.e ((l - 1) • P₂.f) *
    eichler Q P₂.e ((1 : K) • P₁.f)

include h₁₂ in
theorem torusWord_mem (l : K) : torusWord P₁ P₂ l ∈ rootPairSub Q P₁.e P₂.e := by
  have h₂₁ := h₁₂.symm
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup (polar_e_smul_f h₂₁ _))
  · exact rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup (polar_e_smul_f h₁₂ _))
  · exact rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup (polar_e_smul_f h₂₁ _))

omit h₁₂ in
theorem torusWord_mem_orthogonalGroup (P₁ P₂ : HypPair Q) (l : K) :
    torusWord P₁ P₂ l ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (mul_mem (eichler_mem_orthogonalGroup Q _ _) (eichler_mem_orthogonalGroup Q _ _))
    (eichler_mem_orthogonalGroup Q _ _)

include h₁₂ in
theorem torusWord_apply_e {l : K} (hl : l ≠ 0) : torusWord P₁ P₂ l P₁.e = l • P₁.e := by
  have h₂₁ := h₁₂.symm
  simp only [torusWord, LinearEquiv.mul_apply]
  rw [eichler_smul_f_apply_e' h₂₁, map_sub, map_smul, eichler_smul_f_apply_e,
    eichler_smul_f_apply_e' h₁₂, map_sub, map_smul, map_sub, map_smul,
    eichler_smul_f_apply_e' h₂₁, eichler_smul_f_apply_e]
  have : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  linear_combination (norm := module) this • P₂.e

include h₁₂ in
theorem torusWord_apply_f {l : K} (hl : l ≠ 0) : torusWord P₁ P₂ l P₂.f = l • P₂.f := by
  have h₂₁ := h₁₂.symm
  simp only [torusWord, LinearEquiv.mul_apply]
  simp only [map_add, map_smul, eichler_smul_f_apply_f h₂₁, eichler_smul_f_apply_f' h₁₂,
    eichler_smul_f_apply_f h₁₂, eichler_smul_f_apply_f' h₂₁]
  have : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  linear_combination (norm := module) (-(1 : K)) • this • P₁.f

include h₁₂ in
theorem eichler_smul_f_mem_commutator {l : K} (hl0 : l ≠ 0) (hl1 : l * l ≠ 1) (b : K) :
    eichler Q P₁.e (b • P₂.f) ∈ ⁅rootPairSub Q P₁.e P₂.e, rootPairSub Q P₁.e P₂.e⁆ := by
  obtain ⟨s, hs⟩ : ∃ s : K, s = b * (l * l - 1)⁻¹ := ⟨_, rfl⟩
  have hgO := torusWord_mem_orthogonalGroup P₁ P₂ l
  have hconj : torusWord P₁ P₂ l * eichler Q P₁.e (s • P₂.f) * (torusWord P₁ P₂ l)⁻¹ =
      eichler Q P₁.e ((l * s * l) • P₂.f) := by
    rw [eichler_conj hgO, torusWord_apply_e h₁₂ hl0, map_smul, torusWord_apply_f h₁₂ hl0,
      eichler_smul_left, smul_smul, smul_smul]
  have hne : l * l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have hsb : l * s * l - s = b := by
    rw [hs]
    calc l * (b * (l * l - 1)⁻¹) * l - b * (l * l - 1)⁻¹ = b * ((l * l - 1) * (l * l - 1)⁻¹) := by
          ring
      _ = b := by rw [mul_inv_cancel₀ hne, mul_one]
  have hcomm : ⁅torusWord P₁ P₂ l, eichler Q P₁.e (s • P₂.f)⁆ = eichler Q P₁.e (b • P₂.f) := by
    rw [commutatorElement_def, hconj, eichler_inv (polar_e_smul_f h₁₂ s),
      eichler_mul (polar_e_smul_f h₁₂ _)
        (by rw [polar_neg_right, polar_e_smul_f h₁₂ s, neg_zero]),
      ← sub_eq_add_neg, ← sub_smul, hsb]
  rw [← hcomm]
  exact commutatorElement_mem_commutator (torusWord_mem h₁₂ l)
    (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup (polar_e_smul_f h₁₂ s)))

include h₁₂ h₁₃ h₂₃ in
theorem rootGroup_le_commutator_rootPairSub {l : K} (hl0 : l ≠ 0) (hl1 : l * l ≠ 1) :
    rootGroup Q P₁.e ≤ ⁅rootPairSub Q P₁.e P₂.e, rootPairSub Q P₁.e P₂.e⁆ := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := mem_rootGroup.mp hg
  obtain ⟨w, hw⟩ : ∃ w : V, w = x - polar Q x P₁.f • P₁.e - polar Q x P₂.f • P₂.e -
      polar Q x P₂.e • P₂.f := ⟨_, rfl⟩
  have hw₁ : polar Q P₁.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, hx, P₁.polar_ee, h₁₂.ee, h₁₂.ef]
    ring
  have hw₂ : polar Q P₂.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_comm Q P₂.e P₁.e, h₁₂.ee, P₂.polar_ee,
      P₂.polar_ef, polar_comm Q P₂.e x]
    ring
  have hw₂' : polar Q P₂.f w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_comm Q P₂.f P₁.e, h₁₂.ef, P₂.polar_fe,
      P₂.polar_ff, polar_comm Q P₂.f x]
    ring
  have hdecomp : x = (polar Q x P₂.e • P₂.f + ((w - Q w • P₂.e) +
      (polar Q x P₂.f + Q w) • P₂.e)) + polar Q x P₁.f • P₁.e := by
    rw [hw]
    module
  have h1 : polar Q P₁.e (polar Q x P₂.e • P₂.f) = 0 := polar_e_smul_f h₁₂ _
  have h2 : polar Q P₁.e (w - Q w • P₂.e) = 0 := by
    rw [polar_sub_right, polar_smul_right_eq, hw₁, h₁₂.ee, mul_zero, sub_zero]
  have h3 : polar Q P₁.e ((polar Q x P₂.f + Q w) • P₂.e) = 0 := by
    rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  have hprod : eichler Q P₁.e x = eichler Q P₁.e (polar Q x P₂.e • P₂.f) *
      (eichler Q P₁.e (w - Q w • P₂.e) * eichler Q P₁.e ((polar Q x P₂.f + Q w) • P₂.e)) := by
    rw [eichler_mul h2 h3, eichler_mul h1 (by rw [polar_add_right, h2, h3, add_zero])]
    conv_lhs => rw [hdecomp]
    rw [eichler_add_smul_self P₁.Q_e]
  rw [hprod]
  exact mul_mem (eichler_smul_f_mem_commutator h₁₂ hl0 hl1 _)
    (mul_mem (eichler_sub_mem_commutator h₁₂ hw₁ hw₂ hw₂')
      (eichler_smul_e_mem_commutator h₁₂ h₁₃ h₂₃ _))

include h₁₂ h₁₃ h₂₃ in
theorem commutator_rootPairSub {l : K} (hl0 : l ≠ 0) (hl1 : l * l ≠ 1) :
    ⁅rootPairSub Q P₁.e P₂.e, rootPairSub Q P₁.e P₂.e⁆ = rootPairSub Q P₁.e P₂.e := by
  refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
  · exact rootGroup_le_commutator_rootPairSub h₁₂ h₁₃ h₂₃ hl0 hl1
  · have h := rootGroup_le_commutator_rootPairSub h₁₂.symm h₂₃ h₁₃ hl0 hl1
    rwa [rootPairSub_comm P₂.e P₁.e] at h

end Perfect

end CFSG.SeitzReduction.OmegaPilot
