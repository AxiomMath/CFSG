module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf11Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf61DStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf50Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf55Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WOrd0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf27Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf3Members
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf54Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf91MuS4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEApply

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

section Steps

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y}
theorem eq_top_of_thmE_data (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n)
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) (H : Subgroup Y)
    (hCt : Subgroup.centralizer ({t} : Set Y) ≤ H)
    (hdata : ∀ (L L' L₃ : Subgroup Y) (x y w : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) L L' L₃ t x y w →
        Subgroup.centralizer ({x * y} : Set Y) ≤ H) : H = ⊤ := by
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have hY : ∀ (L₃ : Subgroup Y) (x₁ x₂ x₃ : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' L₃ t x₁ x₂ x₃ →
        rLayer (CoreAssembly.conjClass (tightCore R)) (x₁ * x₂) ≤ H := by
    intro L₃ x₁ x₂ x₃ hd'
    exact (Asc77.rLayer_le_centralizer _ _).trans (hdata K K' L₃ x₁ x₂ x₃ hd')
  have hkey := exists_conj_of_dstarComp' hCore.partIHypG hd hperp hCt hY
  have htrans : ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K,
      ∃ h' ∈ H, conjSub h' K = J := by
    intro J hJ
    obtain ⟨w, hw, y, hy, hyw⟩ := hkey J hJ
    have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) :=
      (T3.mem_dstarComp_symm hd.mem hJ).1
    have hM₀ : conjSub y⁻¹ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
      refine ⟨hΩ.conjInvariant y⁻¹ J hJΩ, t, hd.hz, ?_⟩
      have := hw.conj y⁻¹
      have e : y⁻¹ * w * y⁻¹⁻¹ = t := by rw [← hyw]; group
      rwa [e] at this
    obtain ⟨g, hg⟩ := htr (conjSub y⁻¹ J) hM₀.1
    have hgz : g * t * g⁻¹ = t := by
      have h1 := hd.hz.conj g
      rw [hg] at h1
      exact (isUniqueInvolution_of_mem_twinSet hd.hz hM₀).eq h1 |>.symm
    have hgC : g ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hgz]
    refine ⟨y * g, Subgroup.mul_mem _ hy (hCt hgC), ?_⟩
    rw [conjSub_mul, hg, conjSub_conjSub_inv]
  have hstd : StdCent (CoreAssembly.conjClass (tightCore R)) K H t :=
    hd.stdCent_of_twin hperp hCt
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd'⟩ := hd.exists_datum_of_pair hL hL' hne hR₁ hR₂ hc hx hy ox oy
        exact hdata L L' L₃ x y w hd'
  exact TwinDisc.thmE_apply (hE hcit hP) hStd.perp.core.toHyp hd.mem hd.hz hstd htrans

theorem oddCent_eq_of_datum' (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (hP : PerpHypS n Y R S t)
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hK₄ : K₄ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (h43 : K₄ ≠ K₃) (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({t} : Set Y)) =
      oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) := by
  have hΩ := d.hyp
  have htc : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by group
      _ = u₁ * (t * u₂) := by rw [← d.comm_z₂]
      _ = (u₁ * t) * u₂ := by group
      _ = (t * u₁) * u₂ := by rw [← d.comm_z₁]
      _ = t * (u₁ * u₂) := by group
  have hut : (u₁ * u₂) * t = t * (u₁ * u₂) := (Subgroup.mem_centralizer_singleton_iff.mp htc).symm
  have hα' : alphaOf (Subgroup.closure ({t, u₁ * u₂} : Set Y)) = ⊥ := by
    rw [Set.pair_comm]; exact hα
  have hmo := movedOddFree_u_of_model hSp hD4 h4 hP d hK₄ h41 h42 h43 htc
  have h1 : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha htc d.hz.sq d.hz.ne_one hα' hmo.2
  have hcomm : oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      Subgroup.centralizer ({t} : Set Y) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact TwinDisc.oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) d.mul_ne_one
      (Subgroup.subset_closure (by simp)) hn
  have hJ2 : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J := h2g
  have hPo2 : InO2C (u₁ * u₂) t := by
    refine ⟨TwinSecXg.twinJoin (CoreAssembly.conjClass (tightCore R)) K,
      TwinSecXg.twinJoin_le_centralizer d.hz, ?_, TwinSecXg.twinJoin_isPGroup hΩ hJ2 d.hz, ?_⟩
    · refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact TwinSecXg.twinJoin_normalized hΩ d.hz (g : Y) g.2 (x : Y) hx
    · exact Subgroup.mul_mem _ (TwinSecXg.le_twinJoin ⟨d.mem, t, d.hz, d.hz⟩ d.hu₁.1)
        (TwinSecXg.le_twinJoin d.hK' d.hu₂.1)
  have h2 : oddCoreIn (Subgroup.centralizer ({u₁ * u₂} : Set Y)) ≤
      oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    oddCoreIn_le_oddCoreIn_of_le
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d.sq_12) hut hcomm hPo2
  exact le_antisymm h1 h2

theorem oddCent_eq_bot_of_thmE (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hPb : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hSp : ModelFactSp62)
    (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n) (hB : V3Hyp51B n) (h5 : V3Fourth n)
    (h7 : V3Alpha13 n) (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have hTri := v3Tri_of_thm4 hcit hPb h4
  have hC := CoreData.of_S hStd.perp.core
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Y, N = oddCoreIn (Subgroup.centralizer ({t} : Set Y)) :=
    ⟨_, rfl⟩
  have hnorm_of : ∀ x : Y, (∀ y ∈ N, x * y * x⁻¹ ∈ N) → (∀ y ∈ N, x⁻¹ * y * x ∈ N) →
      x ∈ Subgroup.normalizer (N : Set Y) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
    have := h2 _ hh
    simpa [mul_assoc] using this
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := by
    intro x hx
    refine hnorm_of x (fun y hy => ?_) (fun y hy => ?_)
    · rw [hN] at hy ⊢
      exact conj_mem_oddCoreIn hx hy
    · rw [hN] at hy ⊢
      have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hx) hy
      simpa using this
  have hdata : ∀ (L L' L₃ : Subgroup Y) (x y w : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) L L' L₃ t x y w →
        Subgroup.centralizer ({x * y} : Set Y) ≤ Subgroup.normalizer (N : Set Y) := by
    intro L L' L₃ x y w hd'
    have std' : V3Std n Y R S t L L' L₃ x y w := ⟨hStd.perp, hStd.two, hStd.exit, hd', hStd.wyl⟩
    obtain ⟨K₄', hF'⟩ := h5 Y R S t L L' L₃ x y w std'
    have hα' := h7 Y R S t L L' L₃ x y w std' K₄' hF' (hTri Y R S t L L' L₃ x y w std' K₄' hF')
    have h2g' := members_isPGroup_of_std hB std' hα'
    have heq := oddCent_eq_of_datum' hSp hD4 h4 hStd.perp hd' hF'.1 hF'.2.1 hF'.2.2.1
      hF'.2.2.2.1 h2g' hα'
    have heq' : N = oddCoreIn (Subgroup.centralizer ({x * y} : Set Y)) := hN.trans heq
    have hmem : ∀ z : Y, z ∈ N ↔ z ∈ oddCoreIn (Subgroup.centralizer ({x * y} : Set Y)) := by
      intro z; rw [heq']
    intro c hc
    refine hnorm_of c (fun z hz => ?_) (fun z hz => ?_)
    · exact (hmem _).2 (conj_mem_oddCoreIn hc ((hmem _).1 hz))
    · have := conj_mem_oddCoreIn (Subgroup.inv_mem _ hc) ((hmem _).1 hz)
      exact (hmem _).2 (by simpa using this)
  have htop : Subgroup.normalizer (N : Set Y) = ⊤ :=
    eq_top_of_thmE_data hE hcit hPb hStd _ hCt hdata
  have hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hodd : Odd (Nat.card N) := by rw [hN]; exact odd_card_oddCoreIn _
  have hle : N ≤ classicalInvolutionOddCore Y := le_sSup ⟨hNn, hodd⟩
  rw [hC.oddFree] at hle
  exact TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn (hN ▸ le_bot_iff.mp hle)

set_option maxHeartbeats 1600000 in
theorem v3LiftsEN_of_hodd (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (hPb : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hB : V3Hyp51B n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
      (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
        ∀ (K₄ : Subgroup Y),
          FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
            alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) = ⊥ →
              classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
                SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) →
                  LongFundSetE3 R t := by
  classical
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd K₄ hF hα hodd hno
  have hd := hStd.datum
  have hΩ := hd.hyp
  have h2g := members_isPGroup_of_std hB hStd hα
  have hq8 := members_q8_of_isPGroup hStd.perp h2g
  have hV := twinSet_four hStd hF
  obtain ⟨M, M', hM, hM', hK₃M, hK₄M', hcomm, hOM, hOM'⟩ :=
    section_lifts hPb hStd.perp hd hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 h2g hα hodd hno
  have hOM0 : classicalInvolutionOddCore ↥M = ⊥ :=
    TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hOM
  have hMcl : IsClassicalMember3 M t :=
    lift_isClassicalMember3 hd hF.1 hF.2.1 hF.2.2.1 hV h2g hq8 hM hK₃M
      (fun a ha b hb => hcomm a ha b (hK₄M' hb)) hOM0
  have hC' := CoreData.of_S hStd.perp.core
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC'.datum
  have hVK : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
      twinSet (CoreAssembly.conjClass (tightCore R)) K :=
    twinSet_eq_of_mem_twinSet hd.hz ⟨CoreAssembly.mem_conjClass_self _, t, hd.hz, hU⟩
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g K₃ = J := by
    obtain ⟨a, ha⟩ := hd.hK₃.1
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have hJt : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsUniqueInvolution J t := fun J hJ => TwinSecXg.isUniqueInvolution_of_mem_twinSet hU hJ
  have hex : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∃ L : Subgroup Y, J ≤ L ∧ IsClassicalMember3 L t := by
    intro J hJ
    obtain ⟨g, hg⟩ := htr J hJ.1
    have hct : g * t * g⁻¹ = t := by
      have h1 := hd.hzK₃.conj g
      rw [hg] at h1
      exact (h1.eq (hJt J hJ))
    refine ⟨conjSub g M, hg ▸ conjSub_mono hK₃M, ?_⟩
    have := hMcl.conj g
    rwa [hct] at this
  choose! Λ hΛ using hex
  rw [hVK] at hΛ
  have hcommTw : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J ≠ J' →
        ∀ a ∈ J', ∀ b ∈ J, a * b = b * a := by
    intro J hJ J' hJ' hne a ha b hb
    have hz1 : IsUniqueInvolution J t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ
    have hz2 : IsUniqueInvolution J' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ'
    have := A7T22.le_trivialOnQuot_of_twin hΩ hJ'.1 hJ.1 (Ne.symm hne) hz2 hz1 ha
    exact commute_of_trivialOnQuot (h2g J hJ.1) this hb
  have hcent : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J ≠ J' →
        ∀ x ∈ J', ∀ l ∈ Λ J, x * l = l * x := by
    intro J hJ J' hJ' hne x hx l hl
    have hz1 : IsUniqueInvolution J t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ
    have hz2 : IsUniqueInvolution J' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ'
    exact centralizes_lift_of_centralizes hΩ hJ.1 hz1 (h2g J hJ.1) (hq8 J hJ.1)
      (hΛ J hJ).2 (hΛ J hJ).1 hodd (hz2.commute_of_mem hx).symm
      (fun j hj => hcommTw J hJ J' hJ' hne x hx j hj) l hl
  refine longFundSetE3_of_lifts hC'.hyp hU hodd Λ (fun J hJ => hΛ J (hVK ▸ hJ)) ?_
  intro J hJ J' hJ' hne x hx y hy
  rw [hVK] at hJ hJ'
  have hz1 : IsUniqueInvolution J t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ
  have hyT : y ∈ Subgroup.centralizer ({t} : Set Y) := isSubnormal_le (hΛ J' hJ').2.subnormal hy
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyT
  have hyJ : ∀ j ∈ J, y * j = j * y := fun j hj =>
    (hcent J' hJ' J hJ (Ne.symm hne) j hj y hy).symm
  exact (centralizes_lift_of_centralizes hΩ hJ.1 hz1 (h2g J hJ.1) (hq8 J hJ.1)
    (hΛ J hJ).2 (hΛ J hJ).1 hodd hyt hyJ x hx).symm

theorem v3SecOrder_three_dvd_adapted (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W) :
    3 ∣ Nat.card (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := by
  have hS := layer_q8Section hin.1.perp hin.1.datum.sq_12
  obtain ⟨W', hW', -, -⟩ := Q3.Q3CP.exists_W_of_hypOmegaGen hS.hyp
    (Classical.arbitrary (Sylow 2 (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))))
  obtain ⟨e⟩ := v3SecMuS4_adapted hin hW hKD hK'D hK₃D hu₁ hu₂ W' hW'
  exact TwinPerp23.W.three_dvd_of_muIsoS4 ⟨e⟩

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
