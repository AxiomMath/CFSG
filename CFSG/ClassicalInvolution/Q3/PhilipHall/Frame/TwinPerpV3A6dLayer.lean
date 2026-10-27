module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dY
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_hull_of_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {M₁ M : Subgroup G} (hM₁ : M₁ ∈ tqMembers3 Ω c) (hM : M ∈ tqMembers3 Ω c)
    (hconj : ∃ g : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      conjSub g (TwinDisc.secImg Ω c M₁) = TwinDisc.secImg Ω c M) :
    ∃ g : ↥(coreHull Ω c), M = conjSub (((g : ↥(Subgroup.centralizer ({c} : Set G))) : G)) M₁ := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := TwinDisc.coreHull Ω c with hX
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  obtain ⟨gb, hgb⟩ := hconj
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective gb
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen (TwinDisc.hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  have hM₁Λ := TwinDisc.subgroupOf_mem_hullFam hM₁
  have hMΛ := TwinDisc.subgroupOf_mem_hullFam hM
  have h1 : (conjSub g₀ (((TwinADescent.coreAt c M₁).subgroupOf C).subgroupOf X)).map
        (QuotientGroup.mk' N₀) =
      (((TwinADescent.coreAt c M).subgroupOf C).subgroupOf X).map (QuotientGroup.mk' N₀) := by
    rw [AscQuot.map_conjSub]
    exact hgb
  obtain ⟨n, -, hnM⟩ :=
    Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd (hΛ.conjInvariant g₀ _ hM₁Λ) hMΛ h1
  refine ⟨n * g₀, TwinDisc.eq_conjSub_of_hull_eq hΩ hc2 hM₁ hM (n * g₀) ?_⟩
  rw [conjSub_mul]
  exact hnM

end Lift


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

section Gen

variable (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
include H

theorem exists_conj_K₃_of_le_centralizer {J : Subgroup Y} (hJ : J ∈ Ω[R])
    (hJc : J ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y)) :
    ∃ g ∈ rLayer Ω[R] (u₁ * u₂), conjSub g K₃ = J := by
  have hd := H.ex.1.datum
  have hΩ := hypOf H
  have hc2 := isPGroup_zpowers_u H
  have hS := TwinPerp23.p23_q8Section H.ex.1.perp hd.sq_12
  obtain ⟨I₆⟩ := H.ae6
  have htr := TwinDisc.AE5.trans_of_aeIdent (by norm_num : 5 ≤ 6) hS I₆
  have hK₃tq : K₃ ∈ tqMembers3 Ω[R] (u₁ * u₂) :=
    mem_tqMembers3_of_le_centralizer hd.hK₃.1 (K₃_le_C H)
  have hJtq : J ∈ tqMembers3 Ω[R] (u₁ * u₂) := mem_tqMembers3_of_le_centralizer hJ hJc
  obtain ⟨gb, hgb⟩ :=
    htr _ (TwinDisc.secImg_mem_secFam hK₃tq) _ (TwinDisc.secImg_mem_secFam hJtq)
  obtain ⟨g, hg⟩ := exists_conj_hull_of_secImg hΩ hc2 hK₃tq hJtq ⟨gb, hgb⟩
  refine ⟨((g : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) : Y), ?_, hg.symm⟩
  exact TwinDisc.coreHull_map_le_rLayer hΩ hc2 ⟨_, g.2, rfl⟩

theorem rLayer_le_pSpan :
    rLayer Ω[R] (u₁ * u₂) ≤ pSpan (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K) := by
  have h2g := h2Of H
  unfold rLayer
  refine iSup₂_le fun Rm hRm => iSup_le fun hRc => ?_
  have hRΩ : Rm ∈ Ω[R] := by rwa [rSet_eq_of_isPGroup h2g] at hRm
  obtain ⟨g, hg, hgJ⟩ := exists_conj_K₃_of_le_centralizer H hRΩ hRc
  obtain ⟨m, hm, hmK⟩ := exists_M_conj_of_mem_D H H.hK₃
  have hgI : g * m ∈ ae6I Ω[R] W (u₁ * u₂) :=
    (ae6I Ω[R] W (u₁ * u₂)).mul_mem (rLayer_le_ae6I _ _ _ hg) (M_le_ae6I _ _ _ hm)
  refine le_pSpan ⟨g * m, hgI, ?_⟩
  rw [conjSub_mul, hmK, hgJ]

end Gen

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
