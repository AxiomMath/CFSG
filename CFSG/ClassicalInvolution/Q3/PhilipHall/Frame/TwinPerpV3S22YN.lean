module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ESup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CNC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ATr3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22X
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CMerge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ETop
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22EW92
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22O

public section

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

variable {n : ℕ}

@[expose] def V3ExitAE6WfN (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    (∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
        V3Std n Y R S t L L' L'' a a' a'' →
        ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' → a ∈ W' → a' ∈ W' →
            ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a')) →
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W →
        K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W → u₁ ∈ W → u₂ ∈ W →
          Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 6) → False

theorem v3UniqSupply_of_openN (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n) (h7 : V3Alpha13 n)
    (hOpen : V3SecOpenW n) (hAE6 : V3ExitAE6WfN n) : V3UniqSupply n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd h2g hNo W' hW' L hL L' hL' hne a ha a' ha' oa oa'
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hTri := v3Tri_of_thm4 hcit hP h4
  have hzL : IsUniqueInvolution L t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hL
  have hzL' : IsUniqueInvolution L' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hL'
  have htW : t ∈ W' := by
    have e := T7A.sq_eq_of_orderOf_four hzL ha.1 oa
    rw [← e]
    exact W'.mul_mem ha.2 ha.2
  have hcomm : Commutes L L' := by
    intro x hx y hy
    have h1 := A7T22.le_trivialOnQuot_of_twin hΩ hL.1 hL'.1 hne hzL hzL' hx
    exact commute_of_trivialOnQuot (h2g L' hL'.1) h1 hy
  have hLsyl : IsSylow2In L L := ⟨le_rfl, h2g L hL.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hL'syl : IsSylow2In L' L' :=
    ⟨le_rfl, h2g L' hL'.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨L₃, w, hd''⟩ := hd.exists_datum_of_pair hL hL' (Ne.symm hne) hLsyl hL'syl hcomm
    ha.1 ha'.1 oa oa'
  have hStd'' : V3Std n Y R S t L L' L₃ a a' w :=
    ⟨hStd.perp, hStd.two, hStd.exit, hd'', hStd.wyl⟩
  obtain ⟨K₄, hF⟩ := h5 Y R S t L L' L₃ a a' w hStd''
  have hα := h7 Y R S t L L' L₃ a a' w hStd'' K₄ hF
    (hTri Y R S t L L' L₃ a a' w hStd'' K₄ hF)
  have hLD := twin_mem_DSet hCore.partIHypG h2g hW' htW hL.1 hzL
  have hL'D := twin_mem_DSet hCore.partIHypG h2g hW' htW hL'.1 hzL'
  have hL₃D := twin_mem_DSet hCore.partIHypG h2g hW' htW hd''.hK₃.1 hd''.hzK₃
  have hno := hNo L L' L₃ a a' w hStd'' W' hW' hLD hL'D hL₃D ha.2 ha'.2
  have hin : V3ExitIn n R S t L L' L₃ a a' w K₄ := ⟨hStd'', hF, hα, h2g, hno⟩
  obtain ⟨-, hW | ⟨m, hm, ⟨I⟩⟩⟩ := v3ExitTrichotomyAd_of_open hcit hP h4 hOpen Y R S t L L' L₃ a a'
    w K₄ hin W' hW' hLD hL'D hL₃D ha.2 ha'.2
  · exact hW
  · rcases hm with rfl | rfl
    · exact (v3ExitAE5W_proved n Y R S t L L' L₃ a a' w K₄ hin W' hW' hLD hL'D hL₃D ha.2 ha'.2
        ⟨I⟩).elim
    · exact (hAE6 Y R S t L L' L₃ a a' w K₄ hNo hin W' hW' hLD hL'D hL₃D ha.2 ha'.2 ⟨I⟩).elim

theorem twinPerpV3E_of_steps42ON
    {n : ℕ}
    (hEW : TwinThmEW.ThmEQ8)
    (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hSec : SecEdgelessConcl163 n) (hSec4 : SecTwinNoRoot n)
    (hGenExC : V3LayerGenExConjAd n)
    (hOpen : V3SecOpenW n) (hAE6 : V3ExitAE6WfN n) (hFin : V3WFinalWg n) :
    TwinPerpV3E n := by
  have hAb' := v3AbelianO2_of_tr h4 (v3AbelianO2Tr_of_split (v3AbelianO2TrS3_of_edgeless hSec)
    (v3AbelianO2TrG4_of_noRoot' hP hcit hSec4))
  have hU3 := v3Hyp51U3E8_of_abelianO2 hAb'
  have hZ := v3ZStar_of_abelianO2 hAb' (v3ZStarSec_proved hP h4)
  have hZW : V3WZStar' n := v3WZStar'_of_core (v3WCore_proved n) v3WAlt2_proved
  have h51 := v3Hyp51U_of_model hSp hD4 hM12 h4 hU3
  have hB := v3Hyp51B_of_vertices h51
  have hStarF := v3Hyp51StarF_of_model hSp hD4 hM12 h4
  have hαF := v3FourthAlphaF_of_star hB hStarF
  have h5 := v3Fourth_of_alphaF hαF
  have hTri := v3Tri_of_thm4 hcit hP h4
  have h7 := v3Alpha1_of_partsWAllC hEW hcit hP h4 hB h5 hαF hStarF
    (v3LayerGenAllC_of_exitConj hcit hP h4 hGenExC)
  have hLay : V3LayerDW n := v3LayerDW_of_thmE hE hcit hP hSp hD4 h4 hB h5 h7
  have hX := v3ExitExclWg_of_branches (v3ExitWO2_of_core (v3ExitWO2Core_proved n))
    (v3ExitWRestWg_of_split
      (v3W92u_of_dstarConnXu (v3DStarConnXu_of_layerDW hEW hcit hP hLay)) hZW hFin)
  have hSup : V3UniqSupply n := v3UniqSupply_of_openN hcit hP h4 h5 h7 hOpen hAE6
  intro Y _ _ R S t h h3
  by_cases hex : TwinE4 Y
  · exact Or.inl hex
  right
  have hW := muWylD4 (hE hcit hP) hB (v3Sigma_proved n) hZ h h3 hex
  obtain ⟨K', K₃, u₁, u₂, u₃, hd⟩ := exists_hyp22G h h3
  have hStd : V3Std n Y R S t (tightCore R) K' K₃ u₁ u₂ u₃ := ⟨h, h3, hex, hd, hW⟩
  obtain ⟨K₄, hF⟩ := h5 Y R S t _ K' K₃ u₁ u₂ u₃ hStd
  have hα := h7 Y R S t _ K' K₃ u₁ u₂ u₃ hStd K₄ hF (hTri Y R S t _ K' K₃ u₁ u₂ u₃ hStd K₄ hF)
  have h2g := members_isPGroup_of_std hB hStd hα
  have hodd := oddCent_eq_bot_of_thmE hE hcit hP hSp hD4 h4 hB h5 h7 hStd
  by_cases hnoEx : ∃ (L L' L'' : Subgroup Y) (a a' a'' : Y),
      V3Std n Y R S t L L' L'' a a' a'' ∧
      ∃ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' ∧
        L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' ∧
        L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' ∧ a ∈ W' ∧ a' ∈ W' ∧
          SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a')
  · obtain ⟨L, L', L'', a, a', a'', hStd'', W', -, -, -, -, -, -, hno⟩ := hnoEx
    obtain ⟨K₄', hF'⟩ := h5 Y R S t L L' L'' a a' a'' hStd''
    have hα' := h7 Y R S t L L' L'' a a' a'' hStd'' K₄' hF'
      (hTri Y R S t L L' L'' a a' a'' hStd'' K₄' hF')
    exact v3LiftsEN_of_hodd hSp hD4 h4 hP hB Y R S t L L' L'' a a' a'' hStd'' K₄' hF' hα' hodd hno
  · obtain ⟨x, y, w, hStd', W, hWset, hKD, hK'D, hK₃D, hx, hy, -⟩ := exists_adapted_v3Std hStd h2g
    obtain ⟨K₄', hF'⟩ := h5 Y R S t _ K' K₃ x y w hStd'
    have hα' := h7 Y R S t _ K' K₃ x y w hStd' K₄' hF' (hTri Y R S t _ K' K₃ x y w hStd' K₄' hF')
    have hno : ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (x * y) := fun hno =>
      hnoEx ⟨_, K', K₃, x, y, w, hStd', W, hWset, hKD, hK'D, hK₃D, hx, hy, hno⟩
    have hUniq := hSup Y R S t _ K' K₃ x y w hStd' h2g
      (fun L L' L'' a a' a'' hStd'' W' hW' hLD hL'D hL''D ha ha' hno'' =>
        hnoEx ⟨L, L', L'', a, a', a'', hStd'', W', hW', hLD, hL'D, hL''D, ha, ha', hno''⟩)
    exact (hX Y R S t _ K' K₃ x y w hStd' K₄' hF' hα' h2g hno W hWset hKD hK'D hK₃D hx hy
      hUniq).elim

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
