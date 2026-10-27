module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open Subgroup

@[expose] def ShapeConds {X : Type*} [Group X] (S A : Subgroup X) (a t y : X) (n : ℕ) : Prop :=
  orderOf a = 2 ^ n ∧ A = zpowers a ⊔ zpowers (t⁻¹ * a * t) ∧
    zpowers a ⊓ zpowers (t⁻¹ * a * t) = ⊥ ∧ a * (t⁻¹ * a * t) = (t⁻¹ * a * t) * a ∧
    t * t = 1 ∧ y * y = 1 ∧ t * y = y * t ∧ t ≠ 1 ∧ y ≠ 1 ∧ t ≠ y ∧
    A ⊓ (zpowers t ⊔ zpowers y) = ⊥ ∧ (∀ x ∈ A, y * x * y = x⁻¹) ∧
    S = A ⊔ zpowers t ⊔ zpowers y

structure QPData {G : Type*} [Group G] (n s₁ s₂ : ℕ) (c₁ c₂ w₁ w₂ h : G) : Prop where
  two_le : 2 ≤ n
  c₁_pow : c₁ ^ (2 ^ n) = 1
  c₂_pow : c₂ ^ (2 ^ n) = 1
  z_ne_one : c₁ ^ (2 ^ (n - 1)) ≠ 1
  z_eq : c₂ ^ (2 ^ (n - 1)) = c₁ ^ (2 ^ (n - 1))
  w₁_sq : w₁ * w₁ = c₁ ^ (2 ^ (n - 1))
  w₂_sq : w₂ * w₂ = c₁ ^ (2 ^ (n - 1))
  w₁_conj : w₁ * c₁ * w₁⁻¹ = c₁⁻¹
  w₂_conj : w₂ * c₂ * w₂⁻¹ = c₂⁻¹
  c₁_c₂ : c₁ * c₂ = c₂ * c₁
  c₁_w₂ : c₁ * w₂ = w₂ * c₁
  w₁_c₂ : w₁ * c₂ = c₂ * w₁
  w₁_w₂ : w₁ * w₂ = w₂ * w₁
  h_c₁ : h * c₁ = c₁ * h
  h_c₂ : h * c₂ = c₂ * h
  s₁_odd : Odd s₁
  s₂_odd : Odd s₂
  h_w₁ : h * w₁ * h⁻¹ = c₁ ^ s₁ * w₁
  h_w₂ : h * w₂ * h⁻¹ = c₂ ^ s₂ * w₂
  h_sq : h * h = c₁ ^ s₁ * c₂ ^ s₂
  inter : zpowers c₁ ⊓ zpowers c₂ ≤ zpowers (c₁ ^ (2 ^ (n - 1)))
  h_not_mem : h ∉ closure ({c₁, c₂} : Set G)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
