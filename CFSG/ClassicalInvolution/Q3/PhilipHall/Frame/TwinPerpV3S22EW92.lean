module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ELayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf49Split

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

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

section W92u



variable {n : ℕ}

@[expose] def V3W92u (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
          ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}) →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∃ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) ∧
            ¬ ∃ P : Subgroup Y, P ≤ Subgroup.centralizer ({t} : Set Y) ∧
              (P.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 P ∧ U ≤ P

theorem v3W92u_of_dstarConnXu (hconn : V3DStarConnXu n) : V3W92u n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hUniq hW hO
  have hin' := hin
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  by_contra hcon
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  push Not at hcon
  have hcond0 : ∀ U ∈ USet Ω, U ≤ Subgroup.centralizer ({t} : Set Y) →
      ∃ P : Subgroup Y, TC.IsNormalTwoIn P t ∧ U ≤ P := by
    intro U hU hUC
    obtain ⟨P, hPC, hPn, hP2, hUP⟩ := hcon U hU hUC
    refine ⟨P, ⟨hPC, hP2, fun c hc p hp => ?_⟩, hUP⟩
    have := hPn.conj_mem ⟨p, hPC hp⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.mp this
  have htr : ∀ J ∈ Ω, ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have hcondL : ∀ L ∈ Ω, ∀ u : Y, IsUniqueInvolution L u → ∀ U ∈ USet Ω,
      U ≤ Subgroup.centralizer ({u} : Set Y) → ∃ P : Subgroup Y, TC.IsNormalTwoIn P u ∧ U ≤ P := by
    intro L hL u hu U hU hUC
    obtain ⟨g, rfl⟩ := htr L hL
    have hug : g * t * g⁻¹ = u := (hd.hz.conj g).eq hu
    subst hug
    have hU₀ : conjSub g⁻¹ U ∈ USet Ω := S19B.conjSub_mem_USet hΩ.conjInvariant hU g⁻¹
    have hU₀C : conjSub g⁻¹ U ≤ Subgroup.centralizer ({t} : Set Y) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have hx' : g⁻¹⁻¹ * x * g⁻¹ ∈ U := hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hUC hx')
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : g⁻¹⁻¹ * x * g⁻¹ * (g * t * g⁻¹) = g⁻¹⁻¹ * (x * t) * g⁻¹ := by group
      have e' : g * t * g⁻¹ * (g⁻¹⁻¹ * x * g⁻¹) = g⁻¹⁻¹ * (t * x) * g⁻¹ := by group
      rw [e, e'] at h1
      have := mul_left_cancel (mul_right_cancel (h1))
      exact this
    obtain ⟨P₀, hP₀, hUP₀⟩ := hcond0 _ hU₀ hU₀C
    refine ⟨conjSub g P₀, hP₀.conj g, ?_⟩
    have h1 := conjSub_mono (n := g) hUP₀
    rwa [conjSub_conjSub_inv] at h1
  have hA : ∀ {M N : Subgroup Y}, (fun M N => N ∈ omegaStarNbr Ω M) M N → M ∈ Ω →
      N ∈ Ω ∧ ∀ z : Y, IsUniqueInvolution M z → TC.UAt Ω z N := by
    intro M N hMN hM
    obtain ⟨hNΩ, -, U, hU, hUN, hUnorm⟩ := hMN
    refine ⟨hNΩ, fun z hz => ?_⟩
    have hUC : U ≤ Subgroup.centralizer ({z} : Set Y) := by
      intro x hx
      have h1 := hz.conj x
      rw [conjSub_eq_of_mem_normalizer (hUnorm hx)] at h1
      have := hz.eq h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * z = (x * z * x⁻¹) * x := by group
        _ = z * x := by rw [← this]
    obtain ⟨P, hP, hUP⟩ := hcondL M hM z hz U hU hUC
    exact ⟨U, hU, hUN, P, hP, hUP⟩
  have hself : ∀ L ∈ Ω, ∀ u : Y, IsUniqueInvolution L u → TC.UAt Ω u L := by
    intro L hL u hu
    have hR : L ∈ RSet Ω := TC.mem_RSet_of_isPGroup hL (h2g L hL)
    have hq := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
    obtain ⟨U, hUR, hc, hcard⟩ := hq.exists_cyclic_index_two
    have hLsyl : IsSylow2In L L := ⟨le_rfl, h2g L hL, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    have hUS : U ∈ USet Ω := mem_USet_of_natCard hL hLsyl hUR hc hcard
    have hUC : U ≤ Subgroup.centralizer ({u} : Set Y) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hu.commute_of_mem (hUR hx)).symm
    obtain ⟨P, hP, hUP⟩ := hcondL L hL u hu U hUS hUC
    exact ⟨U, hUS, hUR, P, hP, hUP⟩
  have hreach : ∀ L ∈ Ω, Relation.ReflTransGen (fun M N => N ∈ omegaStarNbr Ω M) K L := by
    intro L hL
    have hJd := hconn Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin' hUniq L hL
    induction hJd with
    | refl => exact Relation.ReflTransGen.refl
    | tail hb hbc ih =>
      have hbΩ : _ ∈ Ω := (T3.mem_dstarComp_symm hd.mem hb).1
      refine (ih hbΩ).tail ?_
      obtain ⟨hcΩ, h | h⟩ := hbc
      · exact h
      · exact Q3T6.Mu.omegaStarNbr_symm hΩ hcΩ hbΩ h
  have hgen : (⨆ L ∈ Ω, L) = ⊤ := by
    rw [eq_top_iff, ← hCore.gen]
    exact iSup_le fun g => le_iSup₂_of_le (conjSub g (tightCore R)) ⟨g, rfl⟩ le_rfl
  obtain ⟨P, hPn, hP2, htP⟩ := TC.inO2_of_reach hΩ h2g hA hself hd.mem hreach hgen hd.hz
  have hP1 := TwinSecXg.normalTwo_eq_bot_of_fstar_simple hCore.simple hCore.nonab hPn hP2
  rw [hP1] at htP
  exact hd.hz.ne_one (Subgroup.mem_bot.mp htP)

@[expose] def V3WFinalWg (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
      (∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
          ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∀ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) →
            ∀ x : Y, Odd (orderOf x) →
              x ∈ Balance.normalClosureIn (Subgroup.centralizer ({t} : Set Y)) U →
              x ∉ Subgroup.centralizer
                (((⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y)) : Set Y) → False

@[expose] def V3ExitWRestWg (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
      (∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
          ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ → False

theorem v3ExitWRestWg_of_split (h92 : V3W92u n) (hZ : V3WZStar' n) (hF : V3WFinalWg n) :
    V3ExitWRestWg n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hWad hKD hK'D hK₃D hu₁ hu₂ hUniq hO
  have hd := hin.1.datum
  have hW : ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V} :=
    hUniq W hWad K (mem_twinSet_self hd.mem hd.hz) K' hd.hK' (Ne.symm hd.hne) u₁
      ⟨hd.hu₁.1, hu₁⟩ u₂ ⟨hd.hu₂.1, hu₂⟩ hd.hu₁.2 hd.hu₂.2
  obtain ⟨U, hU, hUC, hUP⟩ := h92 Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hUniq hW hO
  obtain ⟨x, hxo, hxL, hxP⟩ := hZ Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  exact hF Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hWad hKD hK'D hK₃D hu₁ hu₂ hUniq hO U hU hUC x hxo hxL hxP

theorem v3ExitExclWg_of_branches (hWO2 : V3ExitWO2 n) (hWR : V3ExitWRestWg n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
        ∀ K₄ : Subgroup Y,
          FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
            alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥ →
              (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) →
                ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
                  ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
                    K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
                    K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
                    K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
                    (∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
                      ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
                      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
                      ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
                        ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
                          WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}) →
                      False := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hα h2g hno W hWad hKD hK'D hK₃D hu₁ hu₂ hUniq
  have hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ := ⟨hStd, hF, hα, h2g, hno⟩
  have hd := hStd.datum
  have hW : ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V} :=
    hUniq W hWad K (mem_twinSet_self hd.mem hd.hz) K' hd.hK' (Ne.symm hd.hne) u₁
      ⟨hd.hu₁.1, hu₁⟩ u₂ ⟨hd.hu₂.1, hu₂⟩ hd.hu₁.2 hd.hu₂.2
  have ho := hWO2 Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW
  have hz2 : t * t = 1 := hd.hz.sq
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hd.sq_12
  have hcomm : t * (u₁ * u₂) = (u₁ * u₂) * t :=
    (Commute.mul_right (show Commute t u₁ from hd.hz.commute_of_mem hd.hu₁.1)
      (show Commute t u₂ from hd.hzK'.commute_of_mem hd.hu₂.1)).eq
  have hα' : alphaOf (Subgroup.closure ({t, u₁ * u₂} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]; exact hα
  have hbot := oddCoreIn_eq_bot_of_inO2_triple hz2 hc2 hcomm ho.2.1 ho.1 ho.2.2.2 ho.2.2.1 hα'
  exact hWR Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hWad hKD hK'D hK₃D hu₁ hu₂ hUniq
    (TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hbot)

end W92u

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
