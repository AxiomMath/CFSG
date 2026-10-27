module

public import CFSG.GH74.Tits83.OctField

public section

namespace CFSG.GH74.Tits83

open scoped commutatorElement

universe u

section Coord

variable {G : Type u} [Group G]

structure OctCoord (U : ℤ → Subgroup G) where
  K : Type u
  [fld : Field K]
  σ : K →+* K
  σ_sq : ∀ t, σ (σ t) = t ^ 2
  X : ℤ → K → G
  X' : ℤ → K → G
  X_mem : ∀ j t, X j t ∈ U j
  X'_mem : ∀ j t, Even j → X' j t ∈ U j
  X_add_odd : ∀ j, Odd j → ∀ t u, X j (t + u) = X j t * X j u
  X'_add : ∀ j, Even j → ∀ t u, X' j (t + u) = X' j t * X' j u
  X_mul_even : ∀ j, Even j → ∀ t u, X j t * X j u = X j (t + u) * X' j (u * σ t)
  X'_comm : ∀ j, Even j → ∀ t u, X' j t * X j u = X j u * X' j t
  bij_odd : ∀ j, Odd j → Function.Bijective (fun t => (⟨X j t, X_mem j t⟩ : U j))
  bij_even : ∀ j (hj : Even j), Function.Bijective
    (fun p : K × K => (⟨X j p.1 * X' j p.2, (U j).mul_mem (X_mem j p.1) (X'_mem j p.2 hj)⟩ : U j))
  c12 : ∀ s, Even s → ∀ t u, X (1 + s) t * X (2 + s) u = X (2 + s) u * X (1 + s) t
  c12' : ∀ s, Even s → ∀ t u, X (1 + s) t * X' (2 + s) u = X' (2 + s) u * X (1 + s) t
  c13 : ∀ s, Even s → ∀ t u, X (1 + s) t * X (3 + s) u = X (3 + s) u * X (1 + s) t
  c14' : ∀ s, Even s → ∀ t u, X (1 + s) t * X' (4 + s) u = X' (4 + s) u * X (1 + s) t
  c15 : ∀ s, Even s → ∀ t u, X (1 + s) t * X (5 + s) u = X (5 + s) u * X (1 + s) t
  c23 : ∀ s, Even s → ∀ t u, X (2 + s) t * X (3 + s) u = X (3 + s) u * X (2 + s) t
  c2'3 : ∀ s, Even s → ∀ t u, X' (2 + s) t * X (3 + s) u = X (3 + s) u * X' (2 + s) t
  c2'4 : ∀ s, Even s → ∀ t u, X' (2 + s) t * X (4 + s) u = X (4 + s) u * X' (2 + s) t
  c2'4' : ∀ s, Even s → ∀ t u, X' (2 + s) t * X' (4 + s) u = X' (4 + s) u * X' (2 + s) t
  c24' : ∀ s, Even s → ∀ t u, X (2 + s) t * X' (4 + s) u = X' (4 + s) u * X (2 + s) t
  c2'5 : ∀ s, Even s → ∀ t u, X' (2 + s) t * X (5 + s) u = X (5 + s) u * X' (2 + s) t
  c26 : ∀ s, Even s → ∀ t u, X (2 + s) t * X (6 + s) u = X (6 + s) u * X (2 + s) t
  c26' : ∀ s, Even s → ∀ t u, X (2 + s) t * X' (6 + s) u = X' (6 + s) u * X (2 + s) t
  c2'6 : ∀ s, Even s → ∀ t u, X' (2 + s) t * X (6 + s) u = X (6 + s) u * X' (2 + s) t
  c2'6' : ∀ s, Even s → ∀ t u, X' (2 + s) t * X' (6 + s) u = X' (6 + s) u * X' (2 + s) t
  r2 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X (4 + s) u⁆ = X' (2 + s) (t * u)
  r3 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X' (6 + s) u⁆ = X' (4 + s) (t * u)
  r4 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X (6 + s) u⁆ =
    X' (2 + s) (σ t * u) * X (3 + s) (t * σ u) * X' (4 + s) (t * σ u * u)
  r5 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X (7 + s) u⁆ =
    X (3 + s) (σ t * u) * X (5 + s) (t * σ u)
  r6 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X' (8 + s) u⁆ =
    X' (2 + s) (σ t * t * u) * X (3 + s) (σ t * t * σ u) * X (4 + s) (σ t * u) *
      X (5 + s) (σ t * t * u ^ 2) * (X (6 + s) (t * u))⁻¹ * X (7 + s) (t * σ u)
  r7 : ∀ s, Even s → ∀ t u, ⁅X (1 + s) t, X (8 + s) u⁆ =
    X (2 + s) (t * u) * X (3 + s) (σ t * t * σ u * u ^ 2) *
      (X (4 + s) (σ t * σ u * u))⁻¹ *
      X (5 + s) (σ t * t * σ u ^ 2 * u ^ 2) * X' (6 + s) (σ t * t * σ u ^ 2 * u ^ 3) *
      X (7 + s) (t * σ u * u ^ 2)
  r8 : ∀ s, Even s → ∀ t u, ⁅X (2 + s) t, X (4 + s) u⁆ = X (3 + s) (t * u)
  r9 : ∀ s, Even s → ∀ t u, ⁅X (2 + s) t, X (5 + s) u⁆ = X' (4 + s) (t * u)
  r10 : ∀ s, Even s → ∀ t u, ⁅X' (2 + s) t, X (7 + s) u⁆ = X' (4 + s) (t * u)
  r11 : ∀ s, Even s → ∀ t u, ⁅X (2 + s) t, X (7 + s) u⁆ =
    X' (4 + s) (σ t * t * u) * X (5 + s) (σ t * u) * X' (6 + s) (t * σ u)
  r12 : ∀ s, Even s → ∀ t u, ⁅X' (2 + s) t, X' (8 + s) u⁆ =
    X' (4 + s) (σ t * u) * X (5 + s) (t * u) * X' (6 + s) (t * σ u)
  r13 : ∀ s, Even s → ∀ t u, ⁅X' (2 + s) t, X (8 + s) u⁆ =
    X (3 + s) (t * u) * X' (4 + s) (σ t * σ u * u) * X' (6 + s) (t * σ u * u ^ 2)
  r14 : ∀ s, Even s → ∀ t u, ⁅X (2 + s) t, X' (8 + s) u⁆ =
    X' (4 + s) (σ t * t ^ 2 * u) * X' (6 + s) (σ t * t * σ u) * X (7 + s) (t * u)
  r15 : ∀ s, Even s → ∀ t u, ⁅X (2 + s) t, X (8 + s) u⁆ =
    X (3 + s) (σ t * t * u) * (X (4 + s) (σ t * u))⁻¹ * X (6 + s) (t * σ u) *
      X (7 + s) (t * σ u * u)

attribute [instance] OctCoord.fld

def OctCoord.toOctField {U : ℤ → Subgroup G} (c : OctCoord U) : OctField U where
  K := c.K
  σ := c.σ
  σ_sq := c.σ_sq
  X := c.X
  X' := c.X'
  X_mem := c.X_mem
  X'_mem := c.X'_mem
  bij_odd := c.bij_odd
  bij_even := c.bij_even

theorem OctCoord.charP {U : ℤ → Subgroup G} (c : OctCoord U) : CharP c.K 2 :=
  c.toOctField.charP

theorem OctCoord.finite [Finite G] {U : ℤ → Subgroup G} (c : OctCoord U) : Finite c.K :=
  c.toOctField.finite

theorem OctCoord.card_odd {U : ℤ → Subgroup G} (c : OctCoord U) {j : ℤ} (hj : Odd j) :
    Nat.card (U j) = Nat.card c.K :=
  c.toOctField.card_odd hj

end Coord

end CFSG.GH74.Tits83
