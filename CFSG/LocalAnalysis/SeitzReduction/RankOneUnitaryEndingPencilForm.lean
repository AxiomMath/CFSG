module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilBasis

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3EndingPencilFormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s : G) (E : Type) [Field E] [Fintype E] [CharP E 2] (σ : E →+* E) (u w : G → E) (d : G)
    (μ : E) (a b χ₁ χ₂ : G → E), U3EndingData G L f t T R₂ U₁ s →
    U3PencilCoords L T R₂ U₁ t f σ u w d μ a χ₁ χ₂ →
    (∀ x ∈ U₁, ∀ y ∈ U₁, b (x * y) = b x + b y) →
    (∀ y ∈ szT₁ L T, ∀ r ∈ R₂, b (y * r) = u y) →
    (∀ x ∈ U₁, b (d * x * d⁻¹) = μ * b x) →
    (∀ x ∈ U₁, b (t * x * t⁻¹) = a x + b x) →
    (∀ x ∈ U₁, a x = 0 → b x = 0 → x ∈ R₂) →
    (∀ α β : E, ∃ x ∈ U₁, a x = α ∧ b x = β) →
      (∃ Z J : Subgroup G, (∀ z ∈ Z, t * z * t⁻¹ ∈ Z → z = 1) ∧
        (∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
          k ∈ normalizer (Z : Set G)) ∧
        J ≤ U₁ ∧ (∀ x ∈ J, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (2 ^ f) ^ 4 ≤ Nat.card J) ∨
      ∃ X : Subgroup G, R₂ ≤ X ∧ X ≤ U₁ ∧ (∀ x ∈ X, x ^ 2 = 1) ∧ (2 ^ f) ^ 4 ≤ Nat.card X ∧
        (∀ x ∈ X, t * x * t⁻¹ ∈ X → x ∈ R₂) ∧
        ∀ Y : Subgroup G, R₂ ≤ Y → Y ≤ U₁ → (∀ y ∈ Y, y ^ 2 = 1) → (2 ^ f) ^ 4 ≤ Nat.card Y →
          Y = X ∨ Y = X.map (MulAut.conj t).toMonoidHom

section Certificates

theorem u3EndingPencilInput_of_form (hform : U3EndingPencilFormInput) : U3EndingPencilInput := by
  intro G _ _ L f t T R₂ U₁ s hD
  obtain ⟨E, _, _, _, σ, u, w, d, μ, a, χ₁, χ₂, hP⟩ := hD.exists_pencilCoords
  obtain ⟨b, h1, h2, h3, h4, h5, h6⟩ := hP.exists_bcoord hD.start hD.card_sylow hD.r2 hD.u1
  exact hform G L f t T R₂ U₁ s E σ u w d μ a b χ₁ χ₂ hD hP h1 h2 h3 h4 h5 h6

theorem u3EndingInput_of_form (hform : U3EndingPencilFormInput) (hsyl : U3EndingSylowInput) :
    U3EndingInput :=
  u3EndingInput_of_pencil (u3EndingPencilInput_of_form hform) hsyl

end Certificates

end CFSG.SeitzReduction.RankOne
