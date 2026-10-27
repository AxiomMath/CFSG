module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Field

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem not_isPGroup_GFE
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup τ K)) (hα : α ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hτ4 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases h3 : τ = .G2 ∧ p = 3
  ·
    obtain ⟨hG2, rfl⟩ := h3
    obtain rfl : τ = ReeTag.G2.tag := hG2
    have : CharP K ReeTag.G2.prime := ringChar.of_eq hchar
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with ⟨g, a, hαg⟩ |
      ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hb, rfl⟩
    · exact not_isPGroup_inner_diagonal hτ4 hK hαg hα
    · exact not_isPGroup_quadratic_field hK2 Nat.prime_three he hKe δ hδ hαg hα
    · exact not_isPGroup_small_ree (hb ▸ hcard) g hα
  · have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
      rcases hτ with h | h | h
      · exact Or.inr (Or.inr ⟨h, fun h' => h3 ⟨h, hchar ▸ h'⟩⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hK hα with ⟨g, a, hαg⟩ |
      ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
    · exact not_isPGroup_inner_diagonal hτ4 hK hαg hα
    · exact not_isPGroup_quadratic_field hK2 hq he hKe δ hδ hαg hα

end CFSG.ComponentClassification.HarrisLit.L33.E1
