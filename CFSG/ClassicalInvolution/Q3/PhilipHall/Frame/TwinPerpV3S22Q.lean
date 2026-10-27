module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22BPf99
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

@[expose] def V3LayerGenExAd (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), u₁ ∈ W → u₂ ∈ W → a₃ ∈ W → a₄ ∈ W →
        ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
          rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ≤
            ((rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({t} : Set Y)) ⊔
              (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ⊓
                Subgroup.centralizer ({y * t * y⁻¹} : Set Y))) ⊔
              oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))

theorem v3LayerGenAllC_of_exit (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hEx : V3LayerGenExAd n) : V3LayerGenAllC n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hW hu₁ hu₂ ha₃ ha₄
  by_cases hno : SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)
  · exact v3LayerGenFr_proved hcit hP h4 Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr hno
  · exact hEx Y R S t K K' K₃ u₁ u₂ u₃ hStd K₄ a₃ a₄ y fr W hW hu₁ hu₂ ha₃ ha₄ hno

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
