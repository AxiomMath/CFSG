module

public import CFSG.LocalAnalysis.GH72.Vocabulary

public section

namespace CFSG.GH72

open Subgroup

namespace Sec3Setting

variable {G : Type*} [Group G] [Finite G]

theorem lemma_3_12 (𝔖 : Sec3Setting G) (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) (T : Subgroup G)
    (g : G) (hT : T.map (MulAut.conj g).toMonoidHom ≤ 𝔖.S) :
    (T ≤ 𝔖.S₁ → ∀ t ∈ T, orderOf t = 2 → g * t * g⁻¹ ∈ 𝔖.S₁) ∧
      (T ≤ 𝔖.S₂ → ∀ t ∈ T, orderOf t = 2 → g * t * g⁻¹ ∈ 𝔖.S₂) := by
  constructor
  · intro hT₁ t ht ht2
    have htS : t ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := (le_sup_left : 𝔖.S₁ ≤ 𝔖.S₁ ⊔ 𝔖.S₂) (hT₁ ht)
    have hgt_map : g * t * g⁻¹ ∈ T.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ht
    have hgtS : g * t * g⁻¹ ∈ 𝔖.S := hT hgt_map
    have hgtS' : g * t * g⁻¹ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq ▸ hgtS
    have hconj : IsConj t (g * t * g⁻¹) := by
      refine ⟨⟨g, g⁻¹, ?_, ?_⟩, ?_⟩
      · simp
      · simp
      · show g * t = (g * t * g⁻¹) * g
        group
    exact ((hpf.separate t htS (g * t * g⁻¹) hgtS' ht2 hconj).1).mp (hT₁ ht)
  · intro hT₂ t ht ht2
    have htS : t ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := (le_sup_right : 𝔖.S₂ ≤ 𝔖.S₁ ⊔ 𝔖.S₂) (hT₂ ht)
    have hgt_map : g * t * g⁻¹ ∈ T.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ht
    have hgtS : g * t * g⁻¹ ∈ 𝔖.S := hT hgt_map
    have hgtS' : g * t * g⁻¹ ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq ▸ hgtS
    have hconj : IsConj t (g * t * g⁻¹) := by
      refine ⟨⟨g, g⁻¹, ?_, ?_⟩, ?_⟩
      · simp
      · simp
      · show g * t = (g * t * g⁻¹) * g
        group
    exact ((hpf.separate t htS (g * t * g⁻¹) hgtS' ht2 hconj).2).mp (hT₂ ht)

end Sec3Setting

end CFSG.GH72
