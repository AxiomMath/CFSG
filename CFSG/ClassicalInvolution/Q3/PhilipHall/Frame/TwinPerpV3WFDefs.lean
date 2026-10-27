module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

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
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Leaves




variable {n : ℕ}

@[expose] def WFOddNormal {Y : Type} [Group Y] (C P N : Subgroup Y) : Prop :=
  N ≤ C ∧ (N.subgroupOf C).Normal ∧ P ≤ N ∧ Odd (P.subgroupOf N).index

@[expose] def WFW0 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
        ∀ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) →
          ∀ x : Y, Odd (orderOf x) →
            x ∈ Balance.normalClosureIn (Subgroup.centralizer ({t} : Set Y)) U →
            x ∉ Subgroup.centralizer
              (((⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y)) : Set Y) →
          ∃ N : Subgroup Y, WFOddNormal (Subgroup.centralizer ({t} : Set Y))
            (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) N ∧ x ∈ N

@[expose] def WFB0 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W' →
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
        ∀ s ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W',
          Subgroup.centralizer ({a * a'} : Set Y) ≤
            Subgroup.normalizer ((Subgroup.closure ({t, s} : Set Y) : Subgroup Y) : Set Y)

@[expose] def WFStepD (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∀ x : Y, Odd (orderOf x) → x * t = t * x →
        (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) →
        (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, ¬ ∀ m ∈ J, x * m = m * x) → False

@[expose] def WFStepC (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∀ x : Y, Odd (orderOf x) → x * t = t * x →
        (∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) →
        (∃ N : Subgroup Y, WFOddNormal (Subgroup.centralizer ({t} : Set Y))
          (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) N ∧ x ∈ N) →
        (∃ J₀ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, (∀ m ∈ J₀, x * m = m * x) ∧
          ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J ≠ J₀ →
            ¬ ∀ m ∈ J, x * m = m * x) → False


@[expose] def WFWM (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∀ (M : Fin 4 → Subgroup Y) (a : Fin 4 → Y) (y : Y),
        WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y →
          ∀ i j : Fin 4, i ≠ j → ∀ vi ∈ M i, vi ∉ W → ∀ vj ∈ M j, vj ∉ W → ∀ k : Fin 4,
            conjSub (vi * vj) (conjSub y (M k)) ≠ conjSub y (M k)

@[expose] def WFD4 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∀ (M : Fin 4 → Subgroup Y) (a : Fin 4 → Y) (y : Y),
        WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y →
          ∃ k : Fin 4 → Y, (∀ i, k i ∈ M i ∧ k i * k i = t) ∧ y⁻¹ * t * y = k 0 * k 1 * k 2 * k 3

end Leaves

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
