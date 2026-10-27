module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerBarHullEquiv layerBarHullEquiv_mk
  mem_coreHull_of_mem_layerX layerX_le_centralizer conjSub_layerX_of_mem layerToHull le_layerX)
open scoped commutatorElement

section Lay

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

structure Lay (Ω : Set (Subgroup G)) (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G)
    (z t u₁ u₂ c : G) : Prop where
  hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂
  hcA : c ∈ cA S R R'
  hc2 : c * c = 1
  hc1 : c ≠ 1
  hbad : BadElt z c
  hT : TwinThmE.T4Supply

namespace Lay

variable (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

theorem hΩ : HypOmegaGen Ω := Λ.hyp.std.1.stand.hyp

theorem hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one Λ.hc2

theorem h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := Λ.hyp.std.1.quot2

theorem hcR : ∀ x ∈ R, c * x = x * c := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp Λ.hcA.2) x (Subgroup.mem_sup_left hx)).symm

theorem hcR' : ∀ x ∈ R', c * x = x * c := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp Λ.hcA.2) x (Subgroup.mem_sup_right hx)).symm

theorem R_le : R ≤ layerX Ω c :=
  le_layerX Λ.hyp.hR.1 fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR x hx).symm

theorem R'_le : R' ≤ layerX Ω c :=
  le_layerX Λ.hyp.hR'.1 fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR' x hx).symm

@[expose] noncomputable def lbe :
    layerBar Ω c ≃* (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  layerBarHullEquiv Λ.hΩ Λ.hc2' Λ.h2

theorem lbe_layerAut {b : G} (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (hb : conjSub b (layerX Ω c) = layerX Ω c) (y : layerBar Ω c) :
    Λ.lbe (C25Y.layerAut (layerX Ω c) hb y) = secAct Λ.hΩ Λ.hc2' ⟨b, hbC⟩ (Λ.lbe y) := by
  induction y using QuotientGroup.induction_on with
  | H y => rfl

end Lay

end Lay

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
