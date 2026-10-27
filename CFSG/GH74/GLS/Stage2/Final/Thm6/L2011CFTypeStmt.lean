module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

structure CFConcl (K : Type) [Group K] [Finite K] (x : K) (q : ℕ) (E₁ E₂ : Subgroup K)
    (X : Subgroup (MulAut K)) : Prop where
  typ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ¬ ((q : ℤ) ≡ ε [ZMOD 8]) ∧ IsLnEps 4 K ε q
  sup : E₁ ⊔ E₂ = Ez x
  comm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a
  inf : E₁ ⊓ E₂ = zpowers x
  sl₁ : HasSL2Model ↥E₁ (fun r => r = q)
  sl₂ : HasSL2Model ↥E₂ (fun r => r = q)
  val2 : (Nat.card ↥(centralizer ({x} : Set K)) / Nat.card ↥(Ez x)).factorization 2 = 2
  cent : ∀ Y : Subgroup (MulAut K), Y ≤ X → (∀ β ∈ Y, β x = x) →
    (∀ γ ∈ X, γ x = x → ∀ β ∈ Y, γ * β * γ⁻¹ ∈ Y) → Odd (Nat.card ↥Y) →
      ∀ β ∈ Y, ∀ k ∈ normalizer (E₁ : Set K), β k = k

@[expose] def CFTypeAut : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → GHList K →
    ∀ x : K, IsCentralInvolution x → ∀ (q : ℕ) (E₁ E₂ : Subgroup K), Ivk93Cfg x q E₁ E₂ →
      ∀ X : Subgroup (MulAut K), (∀ k : K, MulAut.conj k ∈ X) →
        (∃ Y₀ : Subgroup (MulAut K), Y₀ ≤ X ∧ (∀ β ∈ Y₀, β x = x) ∧
            (∀ γ ∈ X, γ x = x → ∀ β ∈ Y₀, γ * β * γ⁻¹ ∈ Y₀) ∧ Odd (Nat.card ↥Y₀) ∧ Y₀ ≠ ⊥) →
        CFConcl K x q E₁ E₂ X

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
