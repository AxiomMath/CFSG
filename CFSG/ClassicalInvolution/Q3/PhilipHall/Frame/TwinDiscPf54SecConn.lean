module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf52DConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf53SigmaNorm

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc


section P4

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_conj_of_secImg_eq_gen (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {M₁ M : Subgroup G}
    (hM₁ : M₁ ∈ tqMembers3 Ω c) (hM : M ∈ tqMembers3 Ω c)
    (h : secImg Ω c M₁ = secImg Ω c M) :
    ∃ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)), M = conjSub n M₁ := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  set Λ : Set (Subgroup ↥X) := hullFam Ω c with hΛdef
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen Λ :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  have hM₁Λ := subgroupOf_mem_hullFam hM₁
  have hMΛ := subgroupOf_mem_hullFam hM
  obtain ⟨n, hn, hMn⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd hM₁Λ hMΛ h
  have hnC : ((n : ↥C) : G) ∈ C := (n : ↥C).2
  refine ⟨((n : ↥C) : G), oddCore_coreHull_le hΩ hc2 hn, ?_⟩
  have h3 := conjSub_subgroupOf X n ((TwinADescent.coreAt c M₁).subgroupOf C)
  rw [h3] at hMn
  have hle2 : conjSub (n : ↥C) ((TwinADescent.coreAt c M₁).subgroupOf C) ≤ X := by
    have := conjSub_mono (n := (n : ↥C)) (le_coreHull hM₁)
    rwa [conjSub_eq_self_of_mem n.2] at this
  have h4 : (TwinADescent.coreAt c M).subgroupOf C =
      conjSub (n : ↥C) ((TwinADescent.coreAt c M₁).subgroupOf C) := by
    have := congrArg (Subgroup.map X.subtype) hMn
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_coreHull hM),
      Subgroup.map_subgroupOf_eq_of_le hle2] at this
  have h5 : conjSub (n : ↥C) ((TwinADescent.coreAt c M₁).subgroupOf C) =
      (TwinADescent.coreAt c (conjSub ((n : ↥C) : G) M₁)).subgroupOf C := by
    rw [conjSub_subgroupOf C (n : ↥C) (TwinADescent.coreAt c M₁),
      TwinADescent.conjSub_coreAt hnC M₁]
  have h6 : TwinADescent.coreAt c M = TwinADescent.coreAt c (conjSub ((n : ↥C) : G) M₁) := by
    have := congrArg (Subgroup.map C.subtype) (h4.trans h5)
    rwa [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c M),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c _)] at this
  exact eq_of_coreAt_eq hΩ hc2 hM (conjSub_mem_tqMembers3 hΩ.conjInvariant hnC hM₁) h6

end P4


section P4b

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem not_dConnected_secFam_of_not_le_sigmaGen
    (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hY : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K) :
    ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore R)) u) := by
  intro hD
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hrY : rLayer Ω u ≤ coreLayer Ω u := rLayer_le_coreLayer hΩ h2 hc2
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJtq : J ∈ tqMembers3 Ω u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have key := exists_conj_tq_of_dConnected hΩ hc2 hJtq
    (fun M hM => hD _ (secImg_mem_secFam hJtq) M hM)
  have hJd : J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz))
  apply hY
  refine hrY.trans (coreLayer_le_of_forall fun M hM => ?_)
  obtain ⟨m, hm, J₁, hJ₁, hJ₁d, rfl⟩ := key M hM
  have hJ₁K : J₁ ∈ dComp Ω K := hJd.trans hJ₁d
  have hmd : conjSub m J₁ ∈ dComp Ω K :=
    conjSub_mem_dComp_of_oddCore_centralizer_u s hα hm hJ₁K
  exact (TwinADescent.coreAt_le_left u _).trans (le_iSup₂_of_le _ hmd le_rfl)

end P4b

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
