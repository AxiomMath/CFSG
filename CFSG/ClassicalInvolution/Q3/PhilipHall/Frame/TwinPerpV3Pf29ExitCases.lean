module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf28O2Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecNoExit

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement

section Exit

section Abstract

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem transitive_of_conj_twin (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (hAA' : ∃ g : X, conjSub g A = A') :
    ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A = M) → M = A' := by
    intro M hM hnot
    have hMA : M ≠ A := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A hA M hM hnot))
  have hcA' : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A' = M) → M = A := by
    intro M hM hnot
    have hMA : M ≠ A' := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A' hA' M hM hnot))
  have hcl : ∀ M ∈ Φ, ∃ g : X, conjSub g A = M := by
    intro M hM
    by_cases h : ∃ g : X, conjSub g A = M
    · exact h
    · obtain ⟨g, hg⟩ := hAA'
      exact ⟨g, hg.trans (hcA M hM h).symm⟩
  intro K hK L hL
  obtain ⟨x, hx⟩ := hcl K hK
  obtain ⟨y, hy⟩ := hcl L hL
  exact ⟨y * x⁻¹, by rw [conjSub_mul, ← hx, conjSub_inv_conjSub, hy]⟩

end Abstract

section V3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

abbrev LSec {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G) : Type :=
  ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)

end V3

section Branches

variable {n : ℕ}

@[expose] def V3ExitIn (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y) : Prop :=
  V3Std n Y R S t K K' K₃ u₁ u₂ u₃ ∧
    FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ ∧
    alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥ ∧
    (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) ∧
    ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)

@[expose] def V3ExitDeg (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (¬ ∃ x : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        conjSub x (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) =
          secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₄) → False

@[expose] def V3ExitWO2 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        InO2C t (u₁ * u₂) ∧ InO2C (u₁ * u₂) t ∧ InO2C t (t * (u₁ * u₂)) ∧ InO2C (t * (u₁ * u₂)) t

end Branches

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
