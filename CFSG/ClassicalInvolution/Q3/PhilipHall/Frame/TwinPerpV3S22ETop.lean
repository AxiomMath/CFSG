module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

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

section Top

@[expose] def V3UniqSupply (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) →
      (∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
        V3Std n Y R S t L L' L'' a a' a'' →
        ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' → a ∈ W' → a' ∈ W' →
            ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a')) →
      ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
          ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}

end Top

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
