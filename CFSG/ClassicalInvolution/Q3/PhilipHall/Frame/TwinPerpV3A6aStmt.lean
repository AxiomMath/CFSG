module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

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


@[expose] def V3ExitAE6Cent (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    (∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
        V3Std n Y R S t L L' L'' a a' a'' →
        ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' → a ∈ W' → a' ∈ W' →
            ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a')) →
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
          Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 6) →
            ∀ (J' L₃ : Subgroup Y) (x₁ x₂ x₃ : Y),
              A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K J' L₃ t x₁ x₂ x₃ →
              (∃ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)), x₁ ∈ W' ∧ x₂ ∈ W') →
                Subgroup.centralizer ({x₁ * x₂} : Set Y) ≤
                  sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
