module

public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups

@[expose] def SL2OddAutTorusSL2 (m : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 5 ≤ Nat.card F → Nat.card F % 4 = m →
    ∀ (Q : Sylow 2 SL(2, F)) (Φ : Subgroup (MulAut SL(2, F))),
      (∀ φ ∈ Φ, ∀ x ∈ (Q : Subgroup SL(2, F)), φ x = x) → (∀ φ ∈ Φ, Odd (orderOf φ)) →
      ∃ h w : SL(2, F), orderOf h = Nat.card F - 1 ∧ w ∈ (Q : Subgroup SL(2, F)) ∧
        w * w ∈ center SL(2, F) ∧ w * w ≠ 1 ∧ (∀ k ∈ zpowers h, w * k * w⁻¹ = k⁻¹) ∧
        normalizer (zpowers h : Set SL(2, F)) = zpowers h ⊔ zpowers w ∧
        ¬ 2 ∣ (zpowers h ⊓ (Q : Subgroup SL(2, F))).relIndex (zpowers h) ∧
        ∀ φ ∈ Φ, ∀ k ∈ zpowers h, φ k ∈ zpowers h

@[expose] def SL2OddAutTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (q : ℕ),
    HasSL2Model ↥K (fun r => r = q) → Odd q → 5 ≤ q →
    ∀ (z : G), (center ↥K).map K.subtype = zpowers z →
    ∀ (Q : Sylow 2 ↥K) (Φ : Subgroup G),
      (∀ f ∈ Φ, ∀ x ∈ K, f * x * f⁻¹ ∈ K) →
      (∀ f ∈ Φ, ∀ x ∈ (Q : Subgroup ↥K).map K.subtype, f * x = x * f) →
      (∀ f ∈ Φ, Odd (orderOf f)) →
      ∃ h w : G, h ∈ K ∧ w ∈ (Q : Subgroup ↥K).map K.subtype ∧ orderOf h = q - 1 ∧ w * w = z ∧
        (∀ k ∈ zpowers h, w * k * w⁻¹ = k⁻¹) ∧
        normalizer (zpowers h : Set G) ⊓ K = zpowers h ⊔ zpowers w ∧
        ¬ 2 ∣ (zpowers h ⊓ (Q : Subgroup ↥K).map K.subtype).relIndex (zpowers h) ∧
        ∀ f ∈ Φ, ∀ k ∈ zpowers h, f * k * f⁻¹ ∈ zpowers h

end CFSG.GH74.GLS.SP.Local
