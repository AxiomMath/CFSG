module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf64Adapt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93Abel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

section

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

variable {n : ℕ}

@[expose] def V3ExitOrbitAd (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ (K₄ : Subgroup Y) (a₃ a₄ y : Y), V3Frame R t K K' K₃ u₁ u₂ K₄ a₃ a₄ y →
        ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), u₁ ∈ W → u₂ ∈ W → a₃ ∈ W → a₄ ∈ W →
        ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
          (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
          ∀ c ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y),
            ∃ g ∈ oddCoreOf (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
              c * t * c⁻¹ = g * t * g⁻¹ ∨ c * t * c⁻¹ = g * (y * t * y⁻¹) * g⁻¹ ∨
                c * t * c⁻¹ = g * (t * (y * t * y⁻¹)) * g⁻¹

end

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

@[expose] def V3AbelianO2TrS3 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃) →
          ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            DbarConnected (CoreAssembly.conjClass (tightCore R)) W →
              ∀ (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
                (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                  ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                    ∃ g, conjSub g M = N) →
                ¬ T3.DStarConnected
                  (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
                  TightInO2 (QuotientGroup.mk'
                    (classicalInvolutionOddCore
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
                    (⟨⟨t, htC⟩, htH⟩ :
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))

@[expose] def V3AbelianO2TrG4 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (¬ ∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃) →
          ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
            DbarConnected (CoreAssembly.conjClass (tightCore R)) W →
              ∀ (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
                (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
                  coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
                (∀ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                  ∀ N ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
                    ∃ g, conjSub g M = N) →
                ¬ T3.DStarConnected
                  (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
                  TightInO2 (QuotientGroup.mk'
                    (classicalInvolutionOddCore
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
                    (⟨⟨t, htC⟩, htH⟩ :
                      ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))

theorem v3AbelianO2Tr_of_split (h3 : V3AbelianO2TrS3 n) (h4 : V3AbelianO2TrG4 n) : V3AbelianO2Tr n := by
  intro Y _ _ R S t hP h3' hE K K' K₃ u₁ u₂ u₃ d W hW hconnW htC htH htrans hconn
  by_cases hV : ∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃
  · exact h3 Y R S t hP h3' hE K K' K₃ u₁ u₂ u₃ d hV W hW hconnW htC htH htrans hconn
  · exact h4 Y R S t hP h3' hE K K' K₃ u₁ u₂ u₃ d hV W hW hconnW htC htH htrans hconn

end

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

@[expose] def V3ExitTrichotomyAd (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
          (∃ M ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
            ∃ zb : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
              IsUniqueInvolution M zb ∧ TightInO2 zb) ∧
            ((∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
              WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) ∨
              ∃ m : ℕ, (m = 5 ∨ m = 6) ∧
                Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) m))

end

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
