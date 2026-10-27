module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type} [Group G]

structure BData (t : G) (x₁ x₂ lam rho tau : G) (B : Subgroup G) (ω : G) : Prop where
  V_le : fourGrp x₁ x₂ ≤ B
  le_Q : B ≤ ctxQ t tau x₁ x₂ rho
  card : Nat.card B = 16
  comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a
  P_comm : ∀ b ∈ B, ∀ p ∈ ctxPL t tau x₁ x₂, b * p * b⁻¹ * p⁻¹ ∈ fourGrp x₁ x₂
  rho_mem : ∀ b ∈ B, rho * b * rho⁻¹ ∈ B
  sig_mem : ∀ b ∈ B, (lam * t) * b * (lam * t)⁻¹ ∈ B
  ω_mem : ω ∈ closure ({t, tau} : Set G)
  ω_ne : ω ≠ 1
  ω_comm : ∀ b ∈ B, ω * b = b * ω

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
