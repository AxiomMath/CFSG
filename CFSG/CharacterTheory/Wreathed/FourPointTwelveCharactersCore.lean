module

public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharactersData

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointTwelveCharacters

namespace ColumnData

variable {ι : Type*} {D : ColumnData ι}

@[expose] def Row8 (D : ColumnData ι) (χ : ι) (p l₁ l₂ l₃ a₁ a₂ a₃ s : ℤ) : Prop :=
  D.P χ = p ∧ D.L₁ χ = l₁ ∧ D.L₂ χ = l₂ ∧ D.L₃ χ = l₃ ∧ D.c₁ χ = a₁ ∧ D.c₂ χ = a₂ ∧
    D.c₃ χ = a₃ ∧ D.cs χ = s

@[expose] def SmallRow (D : ColumnData ι) (ξ : ι) (q σ : ℤ) : Prop :=
  D.P ξ = 0 ∧ D.L₁ ξ = 0 ∧ D.L₂ ξ = q ∧ D.L₃ ξ = 0 ∧ D.c₂ ξ = 0 ∧ D.cs ξ = 0 ∧
    D.c₁ ξ - D.c₃ ξ = 1 ∧ D.c₁ ξ + D.c₃ ξ = σ

theorem sign_pair_select {σ₂ q₂ σ₃ q₃ : ℤ} (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) (hq₂ : q₂ = 1 ∨ q₂ = -1)
    (hσ₃ : σ₃ = 1 ∨ σ₃ = -1) (hq₃ : q₃ = 1 ∨ q₃ = -1)
    (h : (σ₂ - q₂) * (σ₂ - q₂) + (σ₃ - q₃) * (σ₃ - q₃) = 4) :
    (σ₂ = -q₂ ∧ σ₃ = q₃) ∨ (σ₂ = q₂ ∧ σ₃ = -q₃) := by
  rcases hσ₂ with rfl | rfl <;> rcases hq₂ with rfl | rfl <;> rcases hσ₃ with rfl | rfl <;>
    rcases hq₃ with rfl | rfl <;> omega

structure Classified (D : ColumnData ι) (β κ lam γ ψ ξκ ξl : ι) (pβ pκ pl δ ζ : ℤ) : Prop where
  signs : (pβ = 1 ∨ pβ = -1) ∧ (pκ = 1 ∨ pκ = -1) ∧ (pl = 1 ∨ pl = -1) ∧ (δ = 1 ∨ δ = -1) ∧
    (ζ = 1 ∨ ζ = -1)
  B_eq : D.B = {D.p₀, β, κ, lam, γ, ψ, D.η₁, D.cj D.η₁, ξκ, D.cj ξκ, ξl, D.cj ξl}
  nodup : [D.p₀, β, κ, lam, γ, ψ, D.η₁, D.cj D.η₁, ξκ, D.cj ξκ, ξl, D.cj ξl].Nodup
  real : D.cj β = β ∧ D.cj κ = κ ∧ D.cj lam = lam ∧ D.cj γ = γ ∧ D.cj ψ = ψ
  row_β : Row8 D β pβ (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ) (-pβ)
  row_κ : Row8 D κ pκ pκ pκ pκ 0 pκ 0 0
  row_lam : Row8 D lam pl pl pl pl 0 (-pl) 0 0
  row_γ : Row8 D γ 0 0 0 0 (2 * δ) (2 * δ) (2 * δ) (2 * δ)
  row_ψ : Row8 D ψ 0 0 0 0 0 0 0 ζ
  row_η : Row8 D D.η₁ 0 (2 * D.ε) 0 0 0 0 0 0
  row_ξκ : SmallRow D ξκ (-pκ) pκ
  row_ξl : SmallRow D ξl (-pl) (-pl)
  Uim_ξ : D.Uim ξκ = 1 ∧ D.Uim ξl = 1
  deg_P : 1 + pβ * D.d β + pκ * D.d κ + pl * D.d lam = 0
  deg_η : D.ε * D.d D.η₁ = 1 + pβ * D.d β
  deg_γ : δ * D.d γ = -1 - pκ * D.d κ
  deg_ψ : ζ * D.d ψ = 1 + pβ * D.d β + 2 * (pκ * D.d κ)
  deg_ξκ : D.d ξκ = D.d κ
  deg_ξl : D.d ξl = D.d lam
  E_eq : D.B.filter (fun χ => D.P χ ≠ 0) = {D.p₀, β, κ, lam}
  J_eq : D.B.filter (fun χ => D.Q χ ≠ 0) = {ξκ, D.cj ξκ, ξl, D.cj ξl}

end ColumnData

end CFSG.Wreathed.FourPointTwelveCharacters
