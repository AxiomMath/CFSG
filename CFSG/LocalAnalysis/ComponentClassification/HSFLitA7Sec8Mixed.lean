module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MixFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8CaseC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8IIota

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

structure GData (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  h4 : S.Sec4 F T₁
  D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF)
  D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)
  hq₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic
  hq₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic
  hu₁ : D₁.u = F.xF * F.yF
  hu₂ : D₂.u = S.z * F.yF

namespace GData

variable (A : GData S F T₁)

@[expose] noncomputable def V₁ : ISide S F T₁ where
  yi := F.yF
  ki := F.kF
  ui := F.xF * F.yF
  hyi := isRefl_yF F
  hki := isK_kF F
  hui := rfl
  D := A.D₁
  hq := A.hq₁
  hu := A.hu₁

@[expose] noncomputable def V₂ : ISide S F T₁ where
  yi := F.xF * F.yF
  ki := S.z * F.kF
  ui := S.z * F.yF
  hyi := isRefl_xyF F
  hki := isK_zkF F
  hui := (xF_mul_xyF F).symm
  D := A.D₂
  hq := A.hq₂
  hu := A.hu₂

@[expose] noncomputable def P₁ : IPair S F T₁ where
  V := A.V₁
  W := A.V₂
  hyy := Or.inl rfl
  hkk := rfl
  h4 := A.h4

@[expose] noncomputable def P₂ : IPair S F T₁ where
  V := A.V₂
  W := A.V₁
  hyy := Or.inr (by
    change F.yF = S.z * (F.xF * (F.xF * F.yF))
    rw [xF_mul_xyF, ← mul_assoc, z_mul_z, one_mul])
  hkk := by
    change F.kF = S.z * (S.z * F.kF)
    rw [← mul_assoc, z_mul_z, one_mul]
  h4 := A.h4

theorem comm_W : A.V₂.w₁c * A.V₂.vN * A.V₂.w₁c⁻¹ * A.V₂.vN⁻¹ = 1 ∨
    A.V₂.w₁c * A.V₂.vN * A.V₂.w₁c⁻¹ * A.V₂.vN⁻¹ = S.z := by
  rcases A.hq₂ with h | h
  · left
    have hc := A.V₂.w₁c_comm_vN_of (A.P₂.option_of_elem h).2
    rw [hc, mul_inv_cancel_right, mul_inv_cancel]
  · right
    have hc := A.V₂.w₁c_conj_vN_of (A.P₂.option_of_homoc h).2
    rw [hc]
    have hz : S.z * A.V₂.vN = A.V₂.vN * S.z := (A.V₂.vN_comm_E0 (z_mem_E0 _ _)).symm
    rw [← hz]; group

theorem E0W_eq_A (h : A.D₁.q0 = .elem) {e : X}
    (he : e ∈ S.E0 (F.xF * F.yF) (S.z * F.kF)) :
    ∃ ê ∈ MA.E0WList, (A.P₁.ιA h) ê = e := by
  obtain ⟨-, h2, -, -, h5, -, -, h8⟩ := IPair.ιA_spec (P := A.P₁) h
  change (A.P₁.ιA h) MA.u = A.D₁.u at h2
  change (A.P₁.ιA h) MA.k = F.kF at h8
  have hcl : ∀ a ∈ MA.E0WList, ∀ b ∈ MA.E0WList, a * b ∈ MA.E0WList ∧ a⁻¹ ∈ MA.E0WList := by
    decide +kernel
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨MA.z, by decide +kernel, h5⟩
    · exact ⟨MA.u, by decide +kernel, by rw [h2, A.hu₁]⟩
    · exact ⟨MA.z * MA.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
  | one => exact ⟨1, by decide +kernel, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', (hcl a' ha' b' hb').1, map_mul _ _ _⟩
  | inv a _ ha =>
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a'⁻¹, (hcl a' ha' a' ha').2, map_inv _ _⟩

theorem E0W_eq_B (h : A.D₁.q0 = .homocyclic) {e : X}
    (he : e ∈ S.E0 (F.xF * F.yF) (S.z * F.kF)) :
    ∃ ê ∈ MB.E0WList, (A.P₁.ιB h) ê = e := by
  obtain ⟨-, h2, -, -, h5, -, -, h8⟩ := IPair.ιB_spec (P := A.P₁) h
  change (A.P₁.ιB h) MB.u = A.D₁.u at h2
  change (A.P₁.ιB h) MB.k = F.kF at h8
  have hcl : ∀ a ∈ MB.E0WList, ∀ b ∈ MB.E0WList, a * b ∈ MB.E0WList ∧ a⁻¹ ∈ MB.E0WList := by
    decide +kernel
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨MB.z, by decide +kernel, h5⟩
    · exact ⟨MB.u, by decide +kernel, by rw [h2, A.hu₁]⟩
    · exact ⟨MB.z * MB.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
  | one => exact ⟨1, by decide +kernel, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', (hcl a' ha' b' hb').1, map_mul _ _ _⟩
  | inv a _ ha =>
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a'⁻¹, (hcl a' ha' a' ha').2, map_inv _ _⟩

include A in
theorem zk_cases {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers (S.z * F.kF) : Subgroup X)) :
    c = 1 ∨ c = S.z ∨ c = F.kF ∨ c = S.z * F.kF := by
  rcases A.V₂.eq_of_mem_zk hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
  · refine Or.inr (Or.inr (Or.inl ?_))
    change c = S.z * (S.z * F.kF) at h
    rw [h, ← mul_assoc, z_mul_z, one_mul]

theorem false_of_ne (hne : A.D₁.q0 ≠ A.D₂.q0) : False := by
  obtain ⟨c, hct, hw⟩ := A.P₁.exists_w₁W_mixed hne
  obtain ⟨c', hc', hv⟩ := A.P₁.exists_vW_zk
  change A.V₁.w₁c = A.V₂.w₁c * c at hw
  change A.V₁.vN * A.V₁.w₁c = A.V₂.vN * c' at hv
  change c' ∈ (zpowers S.z ⊔ zpowers (S.z * F.kF) : Subgroup X) at hc'
  change c * S.t ∈ S.E0 (F.xF * F.yF) (S.z * F.kF) at hct
  have hw' : A.V₂.w₁c = A.V₁.w₁c * c⁻¹ := by rw [hw]; group
  have hv' : A.V₂.vN = A.V₁.vN * A.V₁.w₁c * c'⁻¹ := by rw [hv]; group
  have hcm := A.comm_W
  rw [hw', hv'] at hcm
  rcases A.hq₁ with h₀ | h₀
  · have h : A.P₁.V.D.q0 = .elem := h₀
    obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := IPair.ιA_spec (P := A.P₁) h
    change (A.P₁.ιA h) MA.w₁ = A.V₁.w₁N at h3
    change (A.P₁.ιA h) MA.v = A.V₁.vN at h4
    change (A.P₁.ιA h) MA.k = F.kF at h8
    obtain ⟨e', he', he⟩ := A.E0W_eq_A h hct
    have hw₁c : A.V₁.w₁c = (A.P₁.ιA h) MA.w₁ := by
      rw [h3]; exact ISide.w₁c_of_elem _ h₀
    have hc : c = (A.P₁.ιA h) (e' * MA.t) := by
      rw [map_mul, he, h7, mul_assoc, t_mul_t, mul_one]
    obtain ⟨c'', hc'', hc''e⟩ : ∃ c'' ∈ MA.ZList, (A.P₁.ιA h) c'' = c' := by
      rcases A.zk_cases hc' with rfl | rfl | rfl | rfl
      · exact ⟨1, by decide +kernel, map_one _⟩
      · exact ⟨MA.z, by decide +kernel, h5⟩
      · exact ⟨MA.k, by decide +kernel, h8⟩
      · exact ⟨MA.z * MA.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
    obtain ⟨n1, nz⟩ := MA.mix_cert e' he' c'' hc''
    rw [hw₁c, hc, ← h4, ← hc''e] at hcm
    simp only [← map_inv, ← map_mul] at hcm
    rcases hcm with hcm | hcm
    · exact n1 ((A.P₁.ιA_injective h) (by rw [hcm, map_one]))
    · exact nz ((A.P₁.ιA_injective h) (by rw [hcm, h5]))
  · have h : A.P₁.V.D.q0 = .homocyclic := h₀
    obtain ⟨-, -, h3, h4, h5, h6, h7, h8⟩ := IPair.ιB_spec (P := A.P₁) h
    change (A.P₁.ιB h) MB.w₁ = A.V₁.w₁N at h3
    change (A.P₁.ιB h) MB.v = A.V₁.vN at h4
    change (A.P₁.ιB h) MB.y = A.V₁.yi at h6
    change (A.P₁.ιB h) MB.k = F.kF at h8
    obtain ⟨e', he', he⟩ := A.E0W_eq_B h hct
    have hw₁c : A.V₁.w₁c = (A.P₁.ιB h) (MB.w₁ * MB.y) := by
      rw [map_mul, h3, h6]; exact ISide.w₁c_of_homoc _ h₀
    have hc : c = (A.P₁.ιB h) (e' * MB.t) := by
      rw [map_mul, he, h7, mul_assoc, t_mul_t, mul_one]
    obtain ⟨c'', hc'', hc''e⟩ : ∃ c'' ∈ MB.ZList, (A.P₁.ιB h) c'' = c' := by
      rcases A.zk_cases hc' with rfl | rfl | rfl | rfl
      · exact ⟨1, by decide +kernel, map_one _⟩
      · exact ⟨MB.z, by decide +kernel, h5⟩
      · exact ⟨MB.k, by decide +kernel, h8⟩
      · exact ⟨MB.z * MB.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
    obtain ⟨n1, nz⟩ := MB.mix_cert e' he' c'' hc''
    rw [hw₁c, hc, ← h4, ← hc''e] at hcm
    simp only [← map_inv, ← map_mul] at hcm
    rcases hcm with hcm | hcm
    · exact n1 ((A.P₁.ιB_injective h) (by rw [hcm, map_one]))
    · exact nz ((A.P₁.ιB_injective h) (by rw [hcm, h5]))

end GData

end Sec8

end CFSG.ComponentClassification.HSFLit
