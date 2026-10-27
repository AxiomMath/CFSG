module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Asc77.AscT8YB2
public import CFSG.ClassicalInvolution.Q3.Q3T7M04
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A02
import CFSG.ClassicalInvolution.Q3.Q3CLWylB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8YY.FrameData :=
  @CFSG.ClassicalInvolution.Asc77.T8YY.FrameData

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_prod_eq_one (c : Q3CL.Thompson.Ctx Ω W) (hclC : Q3CL.ClassicalClause Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W) (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) {zz : Fin 4 → G}
    (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) : zz 0 * zz 1 * zz 2 * zz 3 = 1 :=
  Q3CL.Wyl.frame_prod_eq_one c hclC hnc ρ hne hadj hz

theorem exists_rep_not_mem_dComp (hs : Std8 Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ∃ σ : Rep Ω W, σ.K ∉ dComp Ω K :=
  Q3CL.Wyl.exists_rep_not_mem_dComp hs.toStd8Core hne

theorem mgrp_not_le_sigmaNorm (hs : Std8 Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ MGrp Ω W ≤ sigmaNorm Ω K :=
  Q3CL.Wyl.mgrp_not_le_sigmaNorm hs.toStd8Core hne

theorem exists_frameData (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : Nonempty (FrameData Ω W K J z t) :=
  Q3CL.Wyl.exists_frameData hs.toStd8Core hμ hnc
namespace FrameData
open CFSG.ClassicalInvolution.Asc77.T8YY.FrameData
variable {W K J : Subgroup G} {z t : G}

theorem mgrp_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    MGrp Ω W ≤ Subgroup.centralizer ({F.zz i * F.zz j} : Set G) :=
  Q3CL.Wyl.mgrp_le_centralizer c F i j
end FrameData
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem muIsoWylD4_transfer (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    {W W' : Subgroup G} (hW : W ∈ WSet Ω) (hW' : W' ∈ WSet Ω) (h : MuIsoWylD4 Ω W) :
    MuIsoWylD4 Ω W' := by
  obtain ⟨φ⟩ := h
  obtain ⟨e⟩ := l7_5_2_proved G Ω hΩ W hW W' hW'
  exact ⟨e.symm.trans φ⟩

theorem mgrp_le_H274 (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : MGrp Ω W ≤ T8.H274 Ω K z :=
  Q3CL.Wyl.mgrp_le_H274 hs.toStd8Core hμ hnc

theorem exists_conj_mem_mgrp (hs : Std8 Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSH : (S : Subgroup G) ≤ T8.H274 Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {x : G} (hxL : x ∈ L)
    (hxo : orderOf x = 4) (hxH : x ∈ T8.H274 Ω K z) :
    ∃ y ∈ T8.H274 Ω K z, ∃ m ∈ MGrp Ω W, conjSub y L = conjSub m K :=
  Q3CL.Wyl.exists_conj_mem_mgrp hs.toStd8Core hne hSH hL hxL hxo hxH

theorem mem_H274_of_conj_mem_sylow (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z :=
  Q3CL.Wyl.mem_H274_of_conj_mem_sylow hs.toStd8Core hμ hne hg

theorem mem_H274_of_conj_mem_H274 (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ T8.H274 Ω K z) :
    g ∈ T8.H274 Ω K z :=
  Q3CL.Wyl.mem_H274_of_conj_mem_H274 hs.toStd8Core hμ hne hg

theorem fixesUniqueCoset_z (hs : Std8 Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    FixesUniqueCoset z (T8.H274 Ω K z) :=
  Q3CL.Wyl.fixesUniqueCoset_z hs.toStd8Core hμ hne
end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
