module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14Thm5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Exact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14

namespace TwinDisc

section Exit

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem not_tightEdgeless_top {K₀ : Subgroup X} (hΩ : HypOmegaGen Φ)
    (hΦ : Φ = CoreAssembly.conjClass K₀)
    (htight : tightCore K₀ = K₀) (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) :
    ¬ TightEdgeless (K₀.subgroupOf (⊤ : Subgroup X)) := by
  obtain ⟨M, hM, N, hN⟩ := hedge
  have hc : tightCore (K₀.subgroupOf (⊤ : Subgroup X)) = K₀.subgroupOf (⊤ : Subgroup X) := by
    rw [tightCore_subgroupOf le_top, htight]
  have hfam : restrictFamily Φ (⊤ : Subgroup X) =
      CoreAssembly.conjClass (K₀.subgroupOf (⊤ : Subgroup X)) := by
    ext L'
    constructor
    · rintro ⟨L, hL, -, rfl⟩
      rw [hΦ] at hL
      obtain ⟨g, rfl⟩ := hL
      exact ⟨⟨g, Subgroup.mem_top g⟩, conjSub_subgroupOf _ _ _⟩
    · rintro ⟨g, rfl⟩
      refine ⟨conjSub (g : X) K₀, ?_, le_top, conjSub_subgroupOf _ _ _⟩
      rw [hΦ]
      exact ⟨g, rfl⟩
  intro hE
  unfold TightEdgeless at hE
  rw [hc] at hE
  have hMΦ := hM
  have hNΦ := hN.1
  have h1 := TwinThmE.omegaNbr_subgroupOf hΩ (le_top : M ≤ ⊤) (le_top : N ≤ ⊤) hNΦ hN
  rw [hfam] at h1
  have hM' : M.subgroupOf (⊤ : Subgroup X) ∈
      CoreAssembly.conjClass (K₀.subgroupOf (⊤ : Subgroup X)) := by
    rw [← hfam]; exact subgroupOf_mem_restrictFamily hMΦ le_top
  have hN' : N.subgroupOf (⊤ : Subgroup X) ∈
      CoreAssembly.conjClass (K₀.subgroupOf (⊤ : Subgroup X)) := by
    rw [← hfam]; exact subgroupOf_mem_restrictFamily hNΦ le_top
  exact hE _ hM' _ hN' (Or.inl h1)

theorem twinE4_of_exitSec_tight (hF : Q8TwinFamT X Φ)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hno : ¬ TightInO2 z) {W : Subgroup X} (hKW : K ≤ W)
    (hWs : IsSubnormal W ⊤) (hex : Thm4Twin.F2.ExitSec W K hKW z hz) : TwinE4 X := by
  have hWtop : W = ⊤ := ExitE4.eq_top_of_subnormal hF.sec.gen hF.trans hK hWs rfl hKW
  have hΦ : Φ = CoreAssembly.conjClass K := by
    ext L
    constructor
    · intro hL
      exact hF.trans K hK L hL
    · rintro ⟨g, rfl⟩
      exact hF.sec.hyp.conjInvariant g K hK
  have key : TwinE4 ↥(⊤ : Subgroup X) → TwinE4 X := fun h => ExitE4.twinE4_of_top h
  rcases hex with hE | ⟨S, hnoW, htx⟩
  · exact key (hWtop ▸ hE)
  · have hedge' : ¬ TightEdgeless (K.subgroupOf W) := by
      subst hWtop
      exact not_tightEdgeless_top hF.sec.hyp hΦ (hF.tight K hK) hedge
    rcases htx with h | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hnoW
    · exact absurd h hedge'
    · exact absurd h hedge'
    · exact key (hWtop ▸ TightE4.twinE4 h)

end Exit

theorem oddCent_dichotomy (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {X : Type} [Group X] [Finite X]
    (hlt : Nat.card X < n) {Φ : Set (Subgroup X)} (hF : Q8TwinFamT X Φ)
    (hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) :
    (∃ P : Subgroup X, P.Normal ∧ IsPGroup 2 P ∧ ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u → u ∈ P) ∨
      (∀ w : X, w * w = 1 → oddCoreIn (Subgroup.centralizer ({w} : Set X)) = ⊥) := by
  by_cases hO2 : ∃ K ∈ Φ, ∃ z : X, IsUniqueInvolution K z ∧ TightInO2 z
  · obtain ⟨K', hK', z', hz', P, hPn, hP2, hz'P⟩ := hO2
    refine Or.inl ⟨P, hPn, hP2, ?_⟩
    intro L hL u hu
    obtain ⟨g, hg⟩ := hF.trans K' hK' L hL
    have h1 : IsUniqueInvolution (conjSub g K') (g * z' * g⁻¹) := hz'.conj g
    rw [hg] at h1
    rw [← h1.eq hu]
    exact hPn.conj_mem z' hz'P g
  · push Not at hO2
    refine Or.inr ?_
    by_cases hEx : ∃ K' ∈ Φ, ∃ (z' : X) (hz' : IsUniqueInvolution K' z') (W : Subgroup X)
        (hKW : K' ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : X) K') = W ∧
          Thm4Twin.F2.ExitSec W K' hKW z' hz'
    · obtain ⟨K', hK', z', hz', W, hKW, hWs, -, hexit⟩ := hEx
      have hE4 := twinE4_of_exitSec_tight hF hedge hK' hz' (hO2 K' hK' z' hz') hKW hWs hexit
      intro w hw
      exact oddCent_bot_of_twinE4 hSp hD4 hF.sec.oddFree hE4 hw
    · push Not at hEx
      have hno : TwinExitPf11.NoExitRest X Φ := fun K' hK' z' hz' =>
        ⟨hO2 K' hK' z' hz', fun W hKW hWs hWg => hEx K' hK' z' hz' W hKW hWs hWg⟩
      have hl := TwinExitPf11.hasLifts_of_noExitRest hP hlt hF.sec hF.tight hno
      obtain ⟨M, hM, -⟩ := hedge
      intro w hw
      exact TwinExitPf10.oddCent_bot_of_hasLifts hcit hF.sec.hyp hlt hF.sec.oddFree hF.sec.gen hl
        ⟨M, hM⟩ w hw

theorem exact_of_tight_section (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {X : Type} [Group X] [Finite X]
    (hlt : Nat.card X < n) {Φ : Set (Subgroup X)} (hS : Q8TwinSection X Φ)
    (htight : ∀ K ∈ Φ, tightCore K = K) : ∀ J ∈ Φ, IsPGroup 2 J := by
  have hF := hS.toFamT htight
  obtain ⟨K₀, hK₀, K', hK', hne, J, hJ, -⟩ := hS.triple
  have hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M := ⟨K₀, hK₀, J, hJ⟩
  intro J hJΦ
  obtain ⟨zJ, hzJ⟩ := (hS.hyp.omega1 J hJΦ).1
  refine isPGroup_of_oddCent hS.hyp hJΦ hzJ ?_ (hS.two J hJΦ)
  rcases oddCent_dichotomy hSp hD4 hcit hP hlt hF hedge with ⟨P, hPn, hP2, hmem⟩ | hall
  · exact oddCoreIn_centralizer_eq_bot_of_mem_normal hS.oddFree hPn hP2 (hmem J hJΦ zJ hzJ)
  · exact hall zJ hzJ.sq

@[expose] def NonTightTwin (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), Q8TwinSection X Φ →
    ¬ (∀ K ∈ Φ, tightCore K = K) → T3.DStarConnected Φ

theorem nonExactTwin_of_nonTight (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42)
    {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (h : NonTightTwin n) :
    NonExactTwin n := by
  intro X _ _ hlt Φ hS hex2 _ _
  by_cases ht : ∀ K ∈ Φ, tightCore K = K
  · exact absurd (exact_of_tight_section hSp hD4 hcit hP hlt hS ht) hex2
  · exact h X hlt Φ hS ht

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
