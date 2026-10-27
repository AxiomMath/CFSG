module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_autData (hAut : Foote5AutStructure) :
    ∃ Lin : Subgroup (MulAut (L₀ ⧸ Open.fusionZStar L₀)), Foote5AutData _ Lin :=
  hAut _ h.sec4.footeFamilyType

theorem normalizer_le_normalizer_Q (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hST : IsSylowOf 2 S ⊤) :
    normalizer (S : Set G) ≤ normalizer (Q : Set G) := by
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  intro y hy
  by_contra hyQ
  obtain ⟨x, hxy, x₂, -, hyx, hodd, hx₂S⟩ := exists_odd_mul_of_mem_normalizer hST hy
  have hx : x ∈ normalizer (S : Set G) := zpowers_le.mpr hy hxy
  have hxQ : x ∉ normalizer (Q : Set G) := fun hxQ =>
    hyQ (by rw [hyx]; exact mul_mem hxQ (h.S_le_normalizer_Q hx₂S))
  have hna := h.nonabelian_R ε hGH hKG hD hST hx hxQ
  have hxt := h.conj_t_eq_of_odd ε hD hna hx hxQ hodd
  obtain ⟨g, hgZ, hgR⟩ := h.exists_conj_t_center_not_mem_R ε hD hna hx hxQ hodd hxt hB4 hST
  obtain ⟨n, hn, hny⟩ := Foote47.exists_mem_normalizer_of_isConj hST h.tZ hgZ
    (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  obtain ⟨x₁, hx₁n, x₂', -, hnx, hodd₁, hx₂'S⟩ := exists_odd_mul_of_mem_normalizer hST hn
  have hx₁ : x₁ ∈ normalizer (S : Set G) := zpowers_le.mpr hn hx₁n
  have hconj : x₁⁻¹ * t * x₁ = g⁻¹ * t * g := by
    have h1 : n⁻¹ * t * n = x₂'⁻¹ * (x₁⁻¹ * t * x₁) * x₂' := by rw [hnx]; group
    have h2 := hgZ x₂' hx₂'S
    calc x₁⁻¹ * t * x₁ = x₂' * (x₂'⁻¹ * (x₁⁻¹ * t * x₁) * x₂') * x₂'⁻¹ := by group
      _ = x₂' * (g⁻¹ * t * g) * x₂'⁻¹ := by rw [← h1, ← hny]
      _ = g⁻¹ * t * g := by rw [h2]; group
  by_cases hx₁Q : x₁ ∈ normalizer (Q : Set G)
  · exact hgR (hconj ▸ h.conj_t_mem_R_of_mem_normalizer_Q hx₁ hx₁Q)
  · have h1 := h.conj_t_eq_of_odd ε hD hna hx₁ hx₁Q hodd₁
    apply hgR
    rw [← hconj, show x₁⁻¹ * t * x₁ = t by
      calc x₁⁻¹ * t * x₁ = x₁⁻¹ * (x₁ * t * x₁⁻¹) * x₁ := by rw [h1]
        _ = t := by group]
    exact h.tR

theorem conj_mem_Q_of_center (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hST : IsSylowOf 2 S ⊤) {u g : G}
    (huQ : u ∈ Q) (huZ : ∀ s ∈ S, s * u = u * s)
    (hgZ : ∀ s ∈ S, s * (g⁻¹ * u * g) = g⁻¹ * u * g * s) : g⁻¹ * u * g ∈ Q := by
  obtain ⟨n, hn, hny⟩ := Foote47.exists_mem_normalizer_of_isConj hST huZ hgZ
    (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  rw [hny]
  exact conj_mem_of_mem_normalizer (h.normalizer_le_normalizer_Q hGH hKG hB4 hAut hST hn) huQ

theorem conj_t_mem_R_of_center (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hST : IsSylowOf 2 S ⊤) {g : G}
    (hgZ : ∀ s ∈ S, s * (g⁻¹ * t * g) = g⁻¹ * t * g * s) : g⁻¹ * t * g ∈ S ⊓ L := by
  obtain ⟨n, hn, hny⟩ := Foote47.exists_mem_normalizer_of_isConj hST h.tZ hgZ
    (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  rw [hny]
  exact h.conj_t_mem_R_of_mem_normalizer_Q hn
    (h.normalizer_le_normalizer_Q hGH hKG hB4 hAut hST hn)

end Sec5

end CFSG.ComponentClassification.Foote5
