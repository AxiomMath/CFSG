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

section WSplit2

variable {n : ℕ}

@[expose] def V3WZStar' (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∀ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) →
            (¬ ∃ P : Subgroup Y, P ≤ Subgroup.centralizer ({t} : Set Y) ∧
              (P.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 P ∧ U ≤ P) →
            ∃ x : Y, Odd (orderOf x) ∧ x ∈ Balance.normalClosureIn (Subgroup.centralizer ({t} : Set Y)) U ∧
              x ∉ Subgroup.centralizer (((⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y)) : Set Y)

end WSplit2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
