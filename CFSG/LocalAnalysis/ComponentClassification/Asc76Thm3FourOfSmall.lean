module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourCases

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

@[expose] def SmallTightFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSmall X → ∀ K R S : Subgroup X, TightlyEmbedded K →
    ¬ K.Normal → IsSylowOf 2 R K → IsElemAbelian 2 R → Nat.card R = 4 → IsSylowOf 2 S ⊤ →
    R ≤ S → (∀ g : X, rightConjugate R g ≤ S → rightConjugate R g = R) →
    (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set X))

theorem asc76Theorem3Four_of_small
    (hloc : SmallTightFour) : Asc76Theorem3Four := by
  intro G _ _ K hK hG hO R hR hRd h4 ⟨S, hS, hRS, hwc⟩
  obtain ⟨k, hk, ⟨e⟩⟩ := hRd
  have hcardR : Nat.card R = 2 * 2 ^ (k - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hk2 : k = 2 := by
    have h1 : 2 ^ (k - 1) = 2 ^ 1 := by omega
    have h2 := Nat.pow_right_injective le_rfl h1
    omega
  subst hk2
  have hcomm : ∀ a b : DihedralGroup (2 ^ (2 - 1)), a * b = b * a := by decide
  have hsq : ∀ a : DihedralGroup (2 ^ (2 - 1)), a ^ 2 = 1 := by decide
  have hRe : IsElemAbelian 2 R := by
    refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, hcomm])⟩⟩, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : R) ^ 2 = 1 := e.injective (by rw [map_pow, hsq, map_one])
    simpa using congrArg Subtype.val h1
  have h : Setting K R S := ⟨hK, hG, hO, hR, h4, hRe, hS, hRS, hwc⟩
  by_cases hKn : K.Normal
  · exact Or.inl hKn
  rcases h.cases hKn ⟨e⟩ with h3 | hsm
  · exact Or.inr (Or.inr h3)
  · obtain ⟨h1, h2⟩ := hloc G hsm K R S hK hKn hR hRe h4 hS hRS hwc
    exact Or.inr (Or.inl ⟨hsm, h4, h1, h2⟩)

end CFSG.ComponentClassification.Asc76X.Thm3Four
