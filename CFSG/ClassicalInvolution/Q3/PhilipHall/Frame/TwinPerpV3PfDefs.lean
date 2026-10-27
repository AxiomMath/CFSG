module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.SmallCases.A7T22Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Data

variable {Y : Type} [Group Y]

@[expose] def FourthTwin (Ω : Set (Subgroup Y)) (K K' K₃ : Subgroup Y) (t u₁ u₂ _u₃ : Y)
    (K₄ : Subgroup Y) : Prop :=
  K₄ ∈ twinSet Ω K ∧ K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ ∧
    ∃ g a₁ a₂ a₃ a₄ : Y, a₁ ∈ K ∧ orderOf a₁ = 4 ∧ a₂ ∈ K' ∧ orderOf a₂ = 4 ∧
      a₃ ∈ K₃ ∧ orderOf a₃ = 4 ∧ a₄ ∈ K₄ ∧ orderOf a₄ = 4 ∧
      a₁ * a₂ = a₂ * a₁ ∧ a₁ * a₃ = a₃ * a₁ ∧ a₁ * a₄ = a₄ * a₁ ∧ a₂ * a₃ = a₃ * a₂ ∧
      a₂ * a₄ = a₄ * a₂ ∧ a₃ * a₄ = a₄ * a₃ ∧ g * t * g⁻¹ = a₁ * a₂ * a₃ * a₄ ∧
      alphaOf (Subgroup.closure ({t, g * t * g⁻¹} : Set Y)) =
        alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y))

@[expose] def LayerDataR (Ω : Set (Subgroup Y)) (K₃ K₄ : Subgroup Y) (u : Y) : Prop :=
  rLayer Ω u ≠ ⊤ ∧ (∃ R₃ : Subgroup Y, IsSylow2In R₃ K₃ ∧ R₃ ≤ Subgroup.centralizer ({u} : Set Y)) ∧
    (∃ R₄ : Subgroup Y, IsSylow2In R₄ K₄ ∧ R₄ ≤ Subgroup.centralizer ({u} : Set Y)) ∧
    ∀ R₃ R₄ : Subgroup Y, IsSylow2In R₃ K₃ → IsSylow2In R₄ K₄ →
      R₃ ≤ Subgroup.centralizer ({u} : Set Y) → R₄ ≤ Subgroup.centralizer ({u} : Set Y) →
        (⨆ x : ↥(rLayer Ω u), conjSub (x : Y) R₃) = rLayer Ω u ∧
          R₄ ∈ twinSet {L | ∃ x : ↥(rLayer Ω u), conjSub (x : Y) R₃ = L} R₃

end Data

section Steps

structure V3Std (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) : Prop where
  perp : PerpHypS n Y R S t
  two : ¬ TwoTwins R
  exit : ¬ TwinE4 Y
  datum : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃
  wyl : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
    MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def V3Fourth (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∃ (K₄ : Subgroup Y),
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
