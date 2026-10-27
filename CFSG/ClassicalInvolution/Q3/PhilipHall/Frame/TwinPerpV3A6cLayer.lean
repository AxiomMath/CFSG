module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cIdent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cRho
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cMain
public import CFSG.ClassicalInvolution.Q3.Sec13End16N

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

structure LayerCtx {Y : Type} [Group Y] [Finite Y] (Ω : Set (Subgroup Y)) (c : Y) where
  hΩ : HypOmegaGen Ω
  h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J
  h8 : ∀ J ∈ Ω, Nat.card ↥J = 8
  hc : c * c = 1
  hc1 : c ≠ 1
  hO : oddCoreOf (rLayer Ω c) = ⊥
  I : AEIdent (PY Ω c) 6
  ρ : Y → AE.AEQ 6
  hρ : RhoSpec I (Subgroup.centralizer ({c} : Set Y)) ρ

section Make

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem exists_layerCtx (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    Nonempty (LayerCtx Ω[R] (u₁ * u₂)) := by
  classical
  obtain ⟨hStd, hF, hα, h2g, -⟩ := H.ex
  have hd := hStd.datum
  have hΩ : HypOmegaGen Ω[R] := hd.hyp
  have hc2' : (u₁ * u₂) * (u₁ * u₂) = 1 := hd.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2'
  have hO := A6b.oddCoreOf_rLayer_eq_bot hStd hF hα h2g H.oddC
  have hS := TwinPerpV3.layer_q8Section hStd.perp hc2'
  obtain ⟨I0⟩ := H.ae6
  obtain ⟨I⟩ := nonempty_identY hΩ hc2 h2g hO (TwinDisc.AE5.hgen_of hS) I0
  have hP : pSpan (PY Ω[R] (u₁ * u₂)) ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [pSpan_PY h2g]
    exact TwinPerpV3.rLayer_le_centralizer _ _
  have hperm : ∀ g ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y), ∀ L ∈ PY Ω[R] (u₁ * u₂),
      conjSub g L ∈ PY Ω[R] (u₁ * u₂) := by
    intro g hg L hL
    refine ⟨hΩ.conjInvariant g L hL.1, ?_⟩
    have := conjSub_mono (n := g) hL.2
    rwa [conjSub_eq_self_of_mem hg] at this
  obtain ⟨ρ, hρ⟩ := exists_rhoSpec I _ hP hperm
  exact ⟨⟨hΩ, h2g, A6b.card_member_eq_eight hStd.perp h2g, hc2', hd.mul_ne_one, hO, I, ρ, hρ⟩⟩

end Make

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
