module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.Stage4.HexSL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Hex

@[expose] def T2C3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (F : Type) [Field F] [Finite F], Nat.card F = 3 →
    ∀ (_ : Q ≃* SL2 F) (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
      ∀ φ : MulAut Q, (∀ p ∈ P, φ p = p) → φ = 1

@[expose] def T2OC5 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (e : Q ≃* SL2 F) (P₀ : Sylow 2 Q) (M : Subgroup (MulAut Q)),
    IsPGroup 2 ↥M → (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M →
    (∀ φ ∈ M, (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 (MulAut.congr e φ)).right = 1) →
    (∃ ξ ∈ M, ξ ∉ (MulAut.conj : Q →* MulAut Q).range) →
    ∀ ρ : MulAut Q, Odd (orderOf ρ) → (∀ φ ∈ M, ρ * φ * ρ⁻¹ ∈ M) → ∀ φ ∈ M, ρ * φ = φ * ρ

@[expose] def T2OC3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (F : Type) [Field F] [Finite F], Nat.card F = 3 →
    ∀ (_ : Q ≃* SL2 F) (P₀ : Sylow 2 Q) (M : Subgroup (MulAut Q)),
    IsPGroup 2 ↥M → (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M →
    (∃ ξ ∈ M, ξ ∉ (MulAut.conj : Q →* MulAut Q).range) →
    ∀ ρ : MulAut Q, Odd (orderOf ρ) → (∀ φ ∈ M, ρ * φ * ρ⁻¹ ∈ M) → ∀ φ ∈ M, ρ * φ = φ * ρ

end CFSG.GH74.GLS.Stage4.Rest
