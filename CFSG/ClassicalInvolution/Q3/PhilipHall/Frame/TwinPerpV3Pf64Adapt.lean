module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf24Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Frames

structure V3Frame {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) (K K' K₃ : Subgroup Y)
    (u₁ u₂ : Y) (K₄ : Subgroup Y) (a₃ a₄ y : Y) : Prop where
  hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K
  h41 : K₄ ≠ K
  h42 : K₄ ≠ K'
  h43 : K₄ ≠ K₃
  h3 : a₃ ∈ K₃
  o3 : orderOf a₃ = 4
  h4 : a₄ ∈ K₄
  o4 : orderOf a₄ = 4
  c13 : u₁ * a₃ = a₃ * u₁
  c14 : u₁ * a₄ = a₄ * u₁
  c23 : u₂ * a₃ = a₃ * u₂
  c24 : u₂ * a₄ = a₄ * u₂
  c34 : a₃ * a₄ = a₄ * a₃
  hy : y * t * y⁻¹ = u₁ * u₂ * a₃ * a₄
  hne : y * t * y⁻¹ ≠ t
  hyc : y ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)
  hj : ∃ j : Y, j * u₁ * j⁻¹ = u₁⁻¹ ∧ j * u₂ * j⁻¹ = u₂ ∧ j * a₃ * j⁻¹ = a₃ ∧ j * a₄ * j⁻¹ = a₄

variable {n : ℕ}

@[expose] def V3LayerGenFr (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
          rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
            ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({t} : Set Y)) ⊔
              (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({y * t * y⁻¹} : Set Y))) ⊔
              oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))

theorem V3Frame.fourthTwin (hαF : V3FourthAlphaF n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) {K₄ : Subgroup Y} {a₃ a₄ y : Y}
    (fr : V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y) :
    FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ := by
  have hd := hStd.datum
  exact ⟨fr.hK₄, fr.h41, fr.h42, fr.h43, y, u₁, u₂, a₃, a₄, hd.hu₁.1, hd.hu₁.2, hd.hu₂.1,
    hd.hu₂.2, fr.h3, fr.o3, fr.h4, fr.o4, hd.comm₁₂, fr.c13, fr.c14, fr.c23, fr.c24, fr.c34,
    fr.hy, hαF Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ u₁ u₂ a₃ a₄ y fr.hK₄ fr.h41 fr.h42 fr.h43
      hd.hu₁.1 hd.hu₁.2 hd.hu₂.1 hd.hu₂.2 fr.h3 fr.o3 fr.h4 fr.o4 hd.comm₁₂ fr.c13 fr.c14 fr.c23
      fr.c24 fr.c34 fr.hy fr.hne fr.hyc fr.hj⟩

end Frames

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
