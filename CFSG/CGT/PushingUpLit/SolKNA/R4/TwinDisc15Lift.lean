module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_core_adj_of_sec (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ tqMembers3 Ω c) (hM₂ : M₂ ∈ tqMembers3 Ω c)
    (h : secImg Ω c M₂ ∈ omegaStarNbr (TwinDisc.secFam Ω c) (secImg Ω c M₁)) :
    ∃ o ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)), ∃ U ∈ USet Ω,
      U ≤ TwinADescent.coreAt c M₂ ∧
        U ≤ Subgroup.normalizer ((TwinADescent.coreAt c (conjSub o M₁) : Subgroup G) : Set G) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen (hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  have hΛ' : HypOmegaGen (quotFamily (hullFam Ω c) N₀) :=
    TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hK := subgroupOf_mem_hullFam hM₁
  have hJ := subgroupOf_mem_hullFam hM₂
  obtain ⟨n, hn, hadj⟩ := exists_conj_omegaStarNbr_gen hΛ hΛ' hN₀odd hK hJ h
  have h1 := omegaStarNbr_map hadj
  have h2 := omegaStarNbr_map h1
  have hnC : ((n : ↥C) : G) ∈ C := (n : ↥C).2
  have e1 : (((TwinADescent.coreAt c M₂).subgroupOf C).subgroupOf X).map X.subtype =
      (TwinADescent.coreAt c M₂).subgroupOf C :=
    Subgroup.map_subgroupOf_eq_of_le (le_coreHull hM₂)
  have e2 : ((TwinADescent.coreAt c M₂).subgroupOf C).map C.subtype = TwinADescent.coreAt c M₂ :=
    Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c M₂)
  have e3 : (conjSub n (((TwinADescent.coreAt c M₁).subgroupOf C).subgroupOf X)).map X.subtype =
      conjSub (n : ↥C) ((TwinADescent.coreAt c M₁).subgroupOf C) := by
    rw [← conjSub_map X.subtype n, Subgroup.map_subgroupOf_eq_of_le (le_coreHull hM₁)]
    rfl
  have e4 : (conjSub (n : ↥C) ((TwinADescent.coreAt c M₁).subgroupOf C)).map C.subtype =
      conjSub ((n : ↥C) : G) (TwinADescent.coreAt c M₁) := by
    rw [← conjSub_map C.subtype (n : ↥C),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c M₁)]
    rfl
  rw [e1, e3, e2, e4, TwinADescent.conjSub_coreAt hnC M₁] at h2
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := h2
  exact ⟨((n : ↥C) : G), oddCore_coreHull_le hΩ hc2 hn, U,
    TwinADescent.mem_USet_of_core hc2 hU, hUJ, hUN⟩

end Lift

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
