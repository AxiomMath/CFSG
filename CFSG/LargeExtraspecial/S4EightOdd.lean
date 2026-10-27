module

public import CFSG.LargeExtraspecial.S4EightF6
public import CFSG.LargeExtraspecial.S4EightF4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem timmesfeld_4_8_odd (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) {F : Subgroup S.O}
    (hFodd : Odd (Nat.card F)) (hF1 : F ≠ ⊥) (hFR : F ≤ Rbar S g t)
    (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
    (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1) :
    Nat.card F = 3 ∨ ∃ hVQ : ¬ V S g t ≤ S.Qa g, finrank (ZMod 2) (Vt S g t) = 4 ∧
      (A6Case H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ ∨ PGL25Case H C ht ht1 hVQ) ∧
      ∃ f₁, ∃ hf₁ : f₁ ∈ F, ∃ f₂, ∃ hf₂ : f₂ ∈ F,
        beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) ≠
          0 := by
  rcases card_eq_three_or_exists_beta_ne_zero H hNo C ht ht1 hR hFodd hF1 hFR hLF hCF with
    h3 | ⟨hVQ, hcase, f₁, hf₁, f₂, hf₂, hβ⟩
  · exact Or.inl h3
  right
  refine ⟨hVQ, ?_, ?_, f₁, hf₁, f₂, hf₂, hβ⟩
  · rcases hcase with hSp | hA | hΩ | hP
    · exact (false_of_spCase_of_beta_ne_zero H C ht ht1 hVQ hFodd hFR hLF hNo hSp hf₁ hf₂
        hβ).elim
    · exact hA.finrank_eq
    · have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
      obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
      by_contra h
      exact false_of_omegaCase_of_beta_ne_zero H C ht ht1 hVQ hFodd hFR hLF hΩ (by omega)
        hf₁ hf₂ hβ
    · exact hP.finrank_eq
  · rcases hcase with hSp | hA | hΩ | hP
    · exact (false_of_spCase_of_beta_ne_zero H C ht ht1 hVQ hFodd hFR hLF hNo hSp hf₁ hf₂
        hβ).elim
    · exact Or.inl hA
    · exact Or.inr (Or.inl hΩ)
    · exact Or.inr (Or.inr hP)

end CFSG.LargeExtraspecial.S4
