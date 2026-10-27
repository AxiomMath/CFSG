module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf49Wk

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

section WCore





variable {n : ℕ}

@[expose] def V3WCore (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∀ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) →
            (¬ ∃ P : Subgroup Y, P ≤ Subgroup.centralizer ({t} : Set Y) ∧
              (P.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 P ∧ U ≤ P) →
            ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W ∧ U ≤ W ∧ ∃ w ∈ W,
              W ≤ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) ⊔ Subgroup.zpowers w ∧
                w * w ∈ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M)

theorem v3WDatum_of_core (h : V3WCore n) : V3WDatum n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  obtain ⟨W, hWΩ, htW, hUW, w, hwW, hWw, hw2⟩ :=
    h Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  have hΩ := hin.1.datum.hyp
  have hab := Q3.Q3T6.abelian_of_mem_WSet3 hΩ hWΩ
  refine ⟨W, hWΩ, 1, Subgroup.one_mem _, w, hwW, fun x hx => ?_, ?_, hWw, hw2⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hab x hx t htW)
  · rw [conjSub_one]; exact hUW

theorem v3WZStar'_of_core (h : V3WCore n) (hA : V3WAlt2 n) : V3WZStar' n :=
  v3WZStar'_of_datum (v3WDatum_of_core h) hA

end WCore

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
