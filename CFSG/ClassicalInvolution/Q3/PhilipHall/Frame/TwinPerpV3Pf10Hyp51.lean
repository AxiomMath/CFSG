module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.SmallCases.A7T22Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

section Hyp51

variable {n : ℕ}

@[expose] def V3Hyp51U3 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃) →
            Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂)

end Hyp51

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
