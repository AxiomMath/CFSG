module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abMix
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MixFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abIota
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abPair2

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD}

structure GData (S : KDBase A C) (T₁ : Subgroup X) where
  h4 : S.Sec4 T₁
  D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y)
  D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)
  hq₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic
  hq₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic
  hu₁ : D₁.u = S.x * S.y
  hu₂ : D₂.u = S.z * S.y

variable {S : KDBase A C} {T₁ : Subgroup X}

theorem x_mul_xy (S : KDBase A C) : S.x * (S.x * S.y) = S.z * S.y := by
  rw [← mul_assoc, ← pow_two]; rfl

namespace GData

variable (G : GData S T₁)

@[expose] noncomputable def V₁ : ISide S T₁ where
  yi := S.y
  ki := S.k
  ui := S.x * S.y
  hyi := isRefl_y S
  hki := Or.inl rfl
  hui := rfl
  D := G.D₁
  hq := G.hq₁
  hu := G.hu₁
  h4 := G.h4

@[expose] noncomputable def V₂ : ISide S T₁ where
  yi := S.x * S.y
  ki := S.z * S.k
  ui := S.z * S.y
  hyi := isRefl_xy S
  hki := Or.inr rfl
  hui := (x_mul_xy S).symm
  D := G.D₂
  hq := G.hq₂
  hu := G.hu₂
  h4 := G.h4

@[expose] noncomputable def P₁ : IPair S T₁ where
  V := G.V₁
  W := G.V₂
  hyy := Or.inl rfl
  hkk := rfl

@[expose] noncomputable def P₂ : IPair S T₁ where
  V := G.V₂
  W := G.V₁
  hyy := Or.inr (by
    change S.y = S.z * (S.x * (S.x * S.y))
    rw [x_mul_xy, ← mul_assoc, zz S, one_mul])
  hkk := by
    change S.k = S.z * (S.z * S.k)
    rw [← mul_assoc, zz S, one_mul]

theorem comm_W : G.V₂.w₁c * G.V₂.vN * G.V₂.w₁c⁻¹ * G.V₂.vN⁻¹ = 1 ∨
    G.V₂.w₁c * G.V₂.vN * G.V₂.w₁c⁻¹ * G.V₂.vN⁻¹ = S.z := by
  rcases G.hq₂ with h | h
  · left
    have hc := G.V₂.w₁c_comm_vN_of (G.P₂.option_of_elem h).2
    rw [hc, mul_inv_cancel_right, mul_inv_cancel]
  · right
    have hc := G.V₂.w₁c_conj_vN_of (G.P₂.option_of_homoc h).2
    rw [hc]
    have hz : S.z * G.V₂.vN = G.V₂.vN * S.z := (G.V₂.vN_comm_E0 G.V₂.z_mem_E0).symm
    rw [← hz]; group

theorem E0W_eq_A (h : G.D₁.q0 = .elem) {e : X}
    (he : e ∈ S.E0 (S.x * S.y) (S.z * S.k)) :
    ∃ ê ∈ MA.E0WList, (G.P₁.ιA h) ê = e := by
  obtain ⟨-, h2, -, -, h5, -, -, h8⟩ := IPair.ιA_spec (P := G.P₁) h
  change (G.P₁.ιA h) MA.u = G.D₁.u at h2
  change (G.P₁.ιA h) MA.k = S.k at h8
  have hcl : ∀ a ∈ MA.E0WList, ∀ b ∈ MA.E0WList, a * b ∈ MA.E0WList ∧ a⁻¹ ∈ MA.E0WList := by
    decide +kernel
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨MA.z, by decide +kernel, h5⟩
    · exact ⟨MA.u, by decide +kernel, by rw [h2, G.hu₁]⟩
    · exact ⟨MA.z * MA.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
  | one => exact ⟨1, by decide +kernel, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', (hcl a' ha' b' hb').1, map_mul _ _ _⟩
  | inv a _ ha =>
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a'⁻¹, (hcl a' ha' a' ha').2, map_inv _ _⟩

theorem E0W_eq_B (h : G.D₁.q0 = .homocyclic) {e : X}
    (he : e ∈ S.E0 (S.x * S.y) (S.z * S.k)) :
    ∃ ê ∈ MB.E0WList, (G.P₁.ιB h) ê = e := by
  obtain ⟨-, h2, -, -, h5, -, -, h8⟩ := IPair.ιB_spec (P := G.P₁) h
  change (G.P₁.ιB h) MB.u = G.D₁.u at h2
  change (G.P₁.ιB h) MB.k = S.k at h8
  have hcl : ∀ a ∈ MB.E0WList, ∀ b ∈ MB.E0WList, a * b ∈ MB.E0WList ∧ a⁻¹ ∈ MB.E0WList := by
    decide +kernel
  induction he using closure_induction with
  | mem e he =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨MB.z, by decide +kernel, h5⟩
    · exact ⟨MB.u, by decide +kernel, by rw [h2, G.hu₁]⟩
    · exact ⟨MB.z * MB.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
  | one => exact ⟨1, by decide +kernel, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', (hcl a' ha' b' hb').1, map_mul _ _ _⟩
  | inv a _ ha =>
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a'⁻¹, (hcl a' ha' a' ha').2, map_inv _ _⟩

include G in
theorem zk_cases {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers (S.z * S.k) : Subgroup X)) :
    c = 1 ∨ c = S.z ∨ c = S.k ∨ c = S.z * S.k := by
  rcases G.V₂.eq_of_mem_zk hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))
  · refine Or.inr (Or.inr (Or.inl ?_))
    change c = S.z * (S.z * S.k) at h
    rw [h, ← mul_assoc, zz S, one_mul]

theorem false_of_ne (hne : G.D₁.q0 ≠ G.D₂.q0) : False := by
  obtain ⟨c, hct, hw⟩ := G.P₁.exists_w₁W_mixed hne
  obtain ⟨c', hc', hv⟩ := G.P₁.exists_vW_zk
  change G.V₁.w₁c = G.V₂.w₁c * c at hw
  change G.V₁.vN * G.V₁.w₁c = G.V₂.vN * c' at hv
  change c' ∈ (zpowers S.z ⊔ zpowers (S.z * S.k) : Subgroup X) at hc'
  change c * t ∈ S.E0 (S.x * S.y) (S.z * S.k) at hct
  have hw' : G.V₂.w₁c = G.V₁.w₁c * c⁻¹ := by rw [hw]; group
  have hv' : G.V₂.vN = G.V₁.vN * G.V₁.w₁c * c'⁻¹ := by rw [hv]; group
  have hcm := G.comm_W
  rw [hw', hv'] at hcm
  rcases G.hq₁ with h₀ | h₀
  · have h : G.P₁.V.D.q0 = .elem := h₀
    obtain ⟨-, -, h3, h4, h5, -, h7, h8⟩ := IPair.ιA_spec (P := G.P₁) h
    change (G.P₁.ιA h) MA.w₁ = G.V₁.w₁N at h3
    change (G.P₁.ιA h) MA.v = G.V₁.vN at h4
    change (G.P₁.ιA h) MA.k = S.k at h8
    obtain ⟨e', he', he⟩ := G.E0W_eq_A h hct
    have hw₁c : G.V₁.w₁c = (G.P₁.ιA h) MA.w₁ := by
      rw [h3]; exact ISide.w₁c_of_elem _ h₀
    have hc : c = (G.P₁.ιA h) (e' * MA.t) := by
      rw [map_mul, he, h7, mul_assoc, tt (A := A), mul_one]
    obtain ⟨c'', hc'', hc''e⟩ : ∃ c'' ∈ MA.ZList, (G.P₁.ιA h) c'' = c' := by
      rcases G.zk_cases hc' with rfl | rfl | rfl | rfl
      · exact ⟨1, by decide +kernel, map_one _⟩
      · exact ⟨MA.z, by decide +kernel, h5⟩
      · exact ⟨MA.k, by decide +kernel, h8⟩
      · exact ⟨MA.z * MA.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
    obtain ⟨n1, nz⟩ := MA.mix_cert e' he' c'' hc''
    rw [hw₁c, hc, ← h4, ← hc''e] at hcm
    simp only [← map_inv, ← map_mul] at hcm
    rcases hcm with hcm | hcm
    · exact n1 ((G.P₁.ιA_injective h) (by rw [hcm, map_one]))
    · exact nz ((G.P₁.ιA_injective h) (by rw [hcm, h5]))
  · have h : G.P₁.V.D.q0 = .homocyclic := h₀
    obtain ⟨-, -, h3, h4, h5, h6, h7, h8⟩ := IPair.ιB_spec (P := G.P₁) h
    change (G.P₁.ιB h) MB.w₁ = G.V₁.w₁N at h3
    change (G.P₁.ιB h) MB.v = G.V₁.vN at h4
    change (G.P₁.ιB h) MB.y = G.V₁.yi at h6
    change (G.P₁.ιB h) MB.k = S.k at h8
    obtain ⟨e', he', he⟩ := G.E0W_eq_B h hct
    have hw₁c : G.V₁.w₁c = (G.P₁.ιB h) (MB.w₁ * MB.y) := by
      rw [map_mul, h3, h6]; exact ISide.w₁c_of_homoc _ h₀
    have hc : c = (G.P₁.ιB h) (e' * MB.t) := by
      rw [map_mul, he, h7, mul_assoc, tt (A := A), mul_one]
    obtain ⟨c'', hc'', hc''e⟩ : ∃ c'' ∈ MB.ZList, (G.P₁.ιB h) c'' = c' := by
      rcases G.zk_cases hc' with rfl | rfl | rfl | rfl
      · exact ⟨1, by decide +kernel, map_one _⟩
      · exact ⟨MB.z, by decide +kernel, h5⟩
      · exact ⟨MB.k, by decide +kernel, h8⟩
      · exact ⟨MB.z * MB.k, by decide +kernel, by rw [map_mul, h5, h8]⟩
    obtain ⟨n1, nz⟩ := MB.mix_cert e' he' c'' hc''
    rw [hw₁c, hc, ← h4, ← hc''e] at hcm
    simp only [← map_inv, ← map_mul] at hcm
    rcases hcm with hcm | hcm
    · exact n1 ((G.P₁.ιB_injective h) (by rw [hcm, map_one]))
    · exact nz ((G.P₁.ιB_injective h) (by rw [hcm, h5]))

end GData

variable (S)

theorem gdata_of (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y))
    (h₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) (h₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic) :
    ∃ G : GData S T₁, G.D₁ = D₁ ∧ G.D₂ = D₂ := by
  have ha₁ := act_one_of_abelian (F := frame₁ S) D₁ h₁
  have ha₂ := act_one_of_abelian (F := frame₂ S) D₂ h₂
  exact ⟨⟨h4, D₁, D₂, h₁, h₂, u_eq₁ S h4 D₁ D₂ ha₁ ha₂, u_eq₂ S h4 D₁ D₂ ha₁ ha₂⟩, rfl, rfl⟩

theorem false_of_mixed (h4 : S.Sec4 T₁) (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y))
    (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y))
    (h₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) (h₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic)
    (hne : D₁.q0 ≠ D₂.q0) : False := by
  obtain ⟨G, rfl, rfl⟩ := gdata_of S h4 D₁ D₂ h₁ h₂
  exact G.false_of_ne hne

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
