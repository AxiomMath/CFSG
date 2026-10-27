module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6aStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6aSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ESup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22CStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ELayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

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

theorem v3ExitAE6Cent_proved (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n) (h7 : V3Alpha13 n) (hOpen : V3SecOpenW n) :
    V3ExitAE6Cent n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hNo hin W _ _ _ _ _ _ _ J' L₃ x₁ x₂ x₃ hD ⟨W', hW', hx₁, hx₂⟩
  have hStd := hin.1
  have h2g := hin.2.2.2.1
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hΩc : ConjInvariant (CoreAssembly.conjClass (tightCore R)) := hΩ.conjInvariant
  have hTri := v3Tri_of_thm4 hcit hP h4
  have hStd' : V3Std n Y R S t K J' L₃ x₁ x₂ x₃ :=
    ⟨hStd.perp, hStd.two, hStd.exit, hD, hStd.wyl⟩
  obtain ⟨K₄', hF'⟩ := h5 Y R S t K J' L₃ x₁ x₂ x₃ hStd'
  have hα' := h7 Y R S t K J' L₃ x₁ x₂ x₃ hStd' K₄' hF'
    (hTri Y R S t K J' L₃ x₁ x₂ x₃ hStd' K₄' hF')
  have htW : t ∈ W' := by
    rw [← hD.sq₁]
    exact W'.mul_mem hx₁ hx₁
  have hKD' := twin_mem_DSet hCore.partIHypG h2g hW' htW hD.mem hD.hz
  have hJ'D := twin_mem_DSet hCore.partIHypG h2g hW' htW hD.hK'.1 hD.hzK'
  have hL₃D := twin_mem_DSet hCore.partIHypG h2g hW' htW hD.hK₃.1 hD.hzK₃
  have hno := hNo K J' L₃ x₁ x₂ x₃ hStd' W' hW' hKD' hJ'D hL₃D hx₁ hx₂
  have hin' : V3ExitIn n R S t K J' L₃ x₁ x₂ x₃ K₄' := ⟨hStd', hF', hα', h2g, hno⟩
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K :=
    TwinDisc.centralizer_le_sigmaStarNorm_z hΩ hD.mem hD.hz
  have hconn := v3_secFam_dstarConnected hcit hP h4 hOpen hin' hW' hKD' hJ'D hL₃D hx₁ hx₂
  obtain ⟨hB, -⟩ := v3_tq_members hStd' hF'
  have hc2 : IsPGroup 2 (Subgroup.zpowers (x₁ * x₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hD.sq_12
  have hH : oddCoreOf (Subgroup.centralizer ({x₁ * x₂} : Set Y)) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
    intro g hg
    have hbA : x₁ * x₂ ∈ Subgroup.closure ({x₁ * x₂, t} : Set Y) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have htA : t ∈ Subgroup.closure ({x₁ * x₂, t} : Set Y) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have h1 := TwinDisc.oddCore_comm_of_alpha hα' hbA hD.mul_ne_one htA hg
    exact hCt (Subgroup.mem_centralizer_singleton_iff.mpr h1)
  have hp := TwinDisc.secPath_of_connected hΩ hc2 hB hH
    (fun M hM => hconn _ (secImg_mem_secFam hB) M hM)
  have hL₃S : L₃ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    TwinDisc.mem_dstarComp_of_twin_gen hΩ hD.mem hD.hK₃
  have hmemS : ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      J ≤ Subgroup.centralizer ({x₁ * x₂} : Set Y) →
        J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := fun J hJ hJc =>
    TwinDisc.mem_dstarComp_of_secPath hΩc hD.mem le_rfl
      (hp J (mem_tqMembers3_of_le_centralizer hJ hJc)) hL₃S
  have hLay : rLayer (CoreAssembly.conjClass (tightCore R)) (x₁ * x₂) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
    refine iSup₂_le fun R₀ hR₀ => iSup_le fun hR₀c => ?_
    rw [rSet_eq_of_isPGroup h2g] at hR₀
    exact le_sigmaStarNorm_of_mem_dstarComp hΩc hD.mem (hmemS R₀ hR₀ hR₀c)
  intro c hc
  obtain ⟨γ, hγ, hcγ⟩ := v3_class_of_layer h4 hStd' hF' hc
  have hγc : γ⁻¹ * c ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * t = γ * t * γ⁻¹ * c := by
      calc c * t = (c * t * c⁻¹) * c := by group
        _ = γ * t * γ⁻¹ * c := by rw [hcγ]
    calc (γ⁻¹ * c) * t = γ⁻¹ * (c * t) := by group
      _ = γ⁻¹ * (γ * t * γ⁻¹ * c) := by rw [h1]
      _ = t * (γ⁻¹ * c) := by group
  have h6 := (sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K).mul_mem (hLay hγ) (hCt hγc)
  simpa using h6

theorem dstarConn_of_ae6_of_cent (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hA6 : V3ExitAE6Cent n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    {K₄ : Subgroup Y}
    (hNo : ∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
        V3Std n Y R S t L L' L'' a a' a'' →
        ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' → a ∈ W' → a' ∈ W' →
            ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a'))
    (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    (hI : Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 6)) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
  dstarConn_of_centAdapted hEW hcit hP hin.1
    (hA6 Y R S t K K' K₃ u₁ u₂ u₃ K₄ hNo hin W hW hKD hK'D hK₃D hu₁ hu₂ hI)

theorem dstarConn_of_ae6 (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n)
    (h7 : V3Alpha13 n) (hOpen : V3SecOpenW n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    {K₄ : Subgroup Y}
    (hNo : ∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
        V3Std n Y R S t L L' L'' a a' a'' →
        ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
          L ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' →
          L'' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W' → a ∈ W' → a' ∈ W' →
            ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a'))
    (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W)
    (hI : Nonempty (AEIdent (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) 6)) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
  dstarConn_of_ae6_of_cent hEW hcit hP (v3ExitAE6Cent_proved hcit hP h4 h5 h7 hOpen) hNo hin hW
    hKD hK'D hK₃D hu₁ hu₂ hI

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
