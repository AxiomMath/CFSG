module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.IVK.Defs2

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank

section Lang

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

structure LangHyp (K₁ K₂ : Subgroup H) (z a : H) (e₁ : ↥K₁ ≃* SL2 F₁) (e₂ : ↥K₂ ≃* SL2 F₂)
    (σ₁ : F₁ ≃+* F₁) (σ₂ : F₂ ≃+* F₂) : Prop where
  comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  inter : K₁ ⊓ K₂ = zpowers z
  z_ord : orderOf z = 2
  a_sq : a * a = 1
  norm₁ : ∀ x ∈ K₁, a * x * a⁻¹ ∈ K₁
  norm₂ : ∀ x ∈ K₂, a * x * a⁻¹ ∈ K₂
  odd₁ : Odd (Nat.card F₁) ∧ 3 < Nat.card F₁
  odd₂ : Odd (Nat.card F₂) ∧ 3 < Nat.card F₂
  σ₁_ord : orderOf σ₁ = 2
  σ₂_ord : orderOf σ₂ = 2
  act₁ : ∀ (x : ↥K₁) (hx : a * (x : H) * a⁻¹ ∈ K₁),
    e₁ ⟨a * x * a⁻¹, hx⟩ = stableAut (StatedSL 2 F₁) (fieldStable_statedSL 2) σ₁ (e₁ x)
  act₂ : ∀ (x : ↥K₂) (hx : a * (x : H) * a⁻¹ ∈ K₂),
    e₂ ⟨a * x * a⁻¹, hx⟩ = stableAut (StatedSL 2 F₂) (fieldStable_statedSL 2) σ₂ (e₂ x)

@[expose] def DiagOutE {F : Type} [Field F] (K : Subgroup H) (e : ↥K ≃* SL2 F) (y : H) : Prop :=
  (∀ x ∈ K, y * x * y⁻¹ ∈ K) ∧
    ∃ d : GL (Fin 2) F, ¬ IsSquare ((d : Matrix (Fin 2) (Fin 2) F).det) ∧
      ∀ (x : ↥K) (hx : y * (x : H) * y⁻¹ ∈ K),
        ((e ⟨y * x * y⁻¹, hx⟩ : SL2 F) : GL (Fin 2) F) = d * ((e x : SL2 F) : GL (Fin 2) F) * d⁻¹

end Lang

end CFSG.GH74.GLS.IVK.Prod3
