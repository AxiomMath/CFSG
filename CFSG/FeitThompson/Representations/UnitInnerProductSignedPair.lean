module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

def signedIrr (G : Type*) [Group G] : Set (G → ℂ) := {f | f ∈ Irr G ∨ -f ∈ Irr G}

theorem mem_signedIrr {f : G → ℂ} : f ∈ signedIrr G ↔ f ∈ Irr G ∨ -f ∈ Irr G := Iff.rfl

theorem mem_signedIrr_iff_exists_sign {f : G → ℂ} :
    f ∈ signedIrr G ↔ ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ χ ∈ Irr G, f = ε • χ := by
  constructor
  · rintro (h | h)
    · exact ⟨1, Or.inl rfl, f, h, by simp⟩
    · exact ⟨-1, Or.inr rfl, -f, h, by simp⟩
  · rintro ⟨ε, (rfl | rfl), χ, hχ, rfl⟩
    · exact Or.inl (by simpa using hχ)
    · exact Or.inr (by simpa using hχ)

theorem Irr_subset_signedIrr : Irr G ⊆ signedIrr G := fun _ h => Or.inl h

@[simp] theorem neg_mem_signedIrr_iff {f : G → ℂ} : -f ∈ signedIrr G ↔ f ∈ signedIrr G := by
  simp only [mem_signedIrr, neg_neg]
  exact or_comm

theorem signedIrr_subset_classFun : signedIrr G ⊆ classFun G := by
  rintro f (h | h)
  · exact Irr_subset_classFun h
  · simpa using (classFun G).neg_mem (Irr_subset_classFun h)

theorem signedIrr_subset_virtualChars : signedIrr G ⊆ (virtualChars G : Set (G → ℂ)) := by
  rintro f (h | h)
  · exact Irr_subset_virtualChars h
  · simpa using (virtualChars G).neg_mem (Irr_subset_virtualChars h)

theorem cfInner_smul_right {α : Type*} [Fintype α] (c : ℂ) (f h : α → ℂ) :
    cfInner f (c • h) = conj c * cfInner f h := by
  rw [← conj_cfInner, cfInner_smul_left, map_mul, conj_cfInner]

theorem cfInner_smul_smul_of_mem_Irr [Fintype G] (ε δ : ℂ) {χ ψ : G → ℂ}
    (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    cfInner (ε • χ) (δ • ψ) = if χ = ψ then ε * conj δ else 0 := by
  classical
  rw [cfInner_smul_left, cfInner_smul_right, cfInner_eq_ite_of_mem_Irr hχ hψ]
  split <;> simp

private theorem eq_of_mul_conj_eq_one {δ ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : δ * conj ε = 1) : δ = ε := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hcε : conj ε = ε := by rcases hε with rfl | rfl <;> simp
  rw [hcε] at h
  calc δ = δ * (ε * ε) := by rw [hεε, mul_one]
    _ = (δ * ε) * ε := by ring
    _ = ε := by rw [h, one_mul]

theorem cfInner_self_of_mem_signedIrr [Fintype G] {f : G → ℂ} (hf : f ∈ signedIrr G) :
    cfInner f f = 1 := by
  rcases hf with h | h
  · exact cfInner_self_of_mem_Irr h
  · have := cfInner_self_of_mem_Irr h
    rwa [cfInner_neg_left, cfInner_neg_right, neg_neg] at this

theorem cfInner_eq_zero_or_one_or_neg_one_of_mem_signedIrr [Fintype G] {f h : G → ℂ}
    (hf : f ∈ signedIrr G) (hh : h ∈ signedIrr G) :
    cfInner f h = 0 ∨ cfInner f h = 1 ∨ cfInner f h = -1 := by
  classical
  obtain ⟨ε, hε, χ, hχ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hf
  obtain ⟨δ, hδ, ψ, hψ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hh
  rw [cfInner_smul_smul_of_mem_Irr _ _ hχ hψ]
  split
  · rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp
  · exact Or.inl rfl

theorem eq_of_cfInner_eq_one [Fintype G] {f h : G → ℂ} (hf : f ∈ signedIrr G)
    (hh : h ∈ signedIrr G) (hfh : cfInner f h = 1) : f = h := by
  classical
  obtain ⟨ε, hε, χ, hχ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hf
  obtain ⟨δ, hδ, ψ, hψ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hh
  rw [cfInner_smul_smul_of_mem_Irr _ _ hχ hψ] at hfh
  by_cases hχψ : χ = ψ
  · rw [if_pos hχψ] at hfh
    rw [hχψ, eq_of_mul_conj_eq_one hδ hfh]
  · rw [if_neg hχψ] at hfh
    exact absurd hfh (by norm_num)

theorem eq_or_eq_neg_of_cfInner_sub_eq_one [Fintype G] {ρ σ χ : G → ℂ}
    (hρ : ρ ∈ signedIrr G) (hσ : σ ∈ signedIrr G) (hχ : χ ∈ signedIrr G)
    (hρσ : cfInner ρ σ = 0) (h : cfInner (ρ - σ) χ = 1) : χ = ρ ∨ χ = -σ := by
  classical
  obtain ⟨a, ha, α, hα, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hρ
  obtain ⟨b, hb, β, hβ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hσ
  obtain ⟨c, hc, γ, hγ, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hχ
  rw [cfInner_smul_smul_of_mem_Irr _ _ hα hβ] at hρσ
  rw [cfInner_sub_left, cfInner_smul_smul_of_mem_Irr _ _ hα hγ,
    cfInner_smul_smul_of_mem_Irr _ _ hβ hγ] at h
  have hαβ : α ≠ β := by
    intro he
    rw [if_pos he] at hρσ
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hρσ
  by_cases hαγ : α = γ
  ·
    subst hαγ
    rw [if_pos rfl, if_neg fun he => hαβ he.symm, sub_zero] at h
    exact Or.inl (by rw [eq_of_mul_conj_eq_one hc h])
  · by_cases hβγ : β = γ
    ·
      subst hβγ
      rw [if_neg hαγ, if_pos rfl, zero_sub] at h
      have h' : (-b) * conj c = 1 := by rw [← h]; ring
      rw [← eq_of_mul_conj_eq_one hc h']
      exact Or.inr (by module)
    ·
      rw [if_neg hαγ, if_neg hβγ, sub_zero] at h
      exact absurd h (by norm_num)

end CFSG.FeitThompson
