module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.NT44.AllYCore
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionRootSupport
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem le_core_centralizer_of_mem_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {W : Subgroup G} {a : G}
    (hnonab : ∃ u v : G, u * v ≠ v * u)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (RigidSet fullQ z).ncard ≤ (RigidSet fullQ x).ncard)
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x)))
    (haW : a ∈ W)
    (ha2 : orderOf a = 2) :
    W ≤ (CFSG.Op_p'p 2 ↥(Subgroup.centralizer ({a} : Set G))).map
      (Subgroup.centralizer ({a} : Set G)).subtype := by
  classical
  let Y : Subgroup G := Subgroup.zpowers a
  have ha_ne_one : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    omega
  have hYW : Y ≤ W := by
    simpa [Y] using (Subgroup.zpowers_le.mpr haW)
  have haY : a ∈ Y := Subgroup.mem_zpowers a
  have hYne : Y ≠ ⊥ := by
    intro hY
    have ha_bot : a = 1 := by
      simpa [Y, hY] using haY
    exact ha_ne_one ha_bot
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  let E : Subgroup ↥N := CFSG.pLayer ↥N 2
  have hAll : W ≤ ((CFSG.Op_p'p 2 ↥E).map E.subtype).map N.subtype := by
    simpa [N, E] using
      (CFSG.GH74.GLS.NT44.le_layerCore_normalizer_of_le_rigid_center_sylow
        (G := G) (fullQ := fullQ) (x := x) (W := W) (Y := Y)
        hnonab hx2 hmax hW hYW hYne)
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEchar : E.Characteristic :=
    @CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
      ↥N _ _ 2 hfact2
  have hEnormal : E.Normal := inferInstance
  have hcore : (CFSG.Op_p'p 2 E).map E.subtype = E ⊓ CFSG.Op_p'p 2 ↥N :=
    @CFSG.ABGLocalTools.Op_p'p_map_subtype_eq_inf 2 ↥N _ _ hfact2 E hEnormal
  have hcore_le : (CFSG.Op_p'p 2 E).map E.subtype ≤ CFSG.Op_p'p 2 ↥N := by
    rw [hcore]
    exact inf_le_right
  have hcore_map_le :
      ((CFSG.Op_p'p 2 ↥E).map E.subtype).map N.subtype ≤
        (CFSG.Op_p'p 2 ↥N).map N.subtype :=
    Subgroup.map_mono (f := N.subtype) hcore_le
  have hWcore : W ≤ (CFSG.Op_p'p 2 ↥N).map N.subtype :=
    le_trans hAll hcore_map_le
  have hN : N = Subgroup.centralizer ({a} : Set G) := by
    simpa [N, Y] using
      (CFSG.DisconnectedInvolutionGraph.Helpers.involution_zpowers_normalizer_eq_centralizer
        (G := G) (involution := (⟨a, ha2⟩ : CFSG.DisconnectedInvolutionGraph.Helpers.Involution G)))
  rw [hN] at hWcore
  exact hWcore

end CFSG.GH74.GLS.NT44

end
