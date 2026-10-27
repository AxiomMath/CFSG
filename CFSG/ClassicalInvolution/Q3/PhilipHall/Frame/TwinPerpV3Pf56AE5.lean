module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section AE5Mu

variable {n : ℕ}

@[expose] def V3SecMuS4 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        MuIsoS4 (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) W

@[expose] def V3SecAE5MuE4 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 5) →
        ∃ W ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
          MuIsoE4 (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) W

end AE5Mu

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
