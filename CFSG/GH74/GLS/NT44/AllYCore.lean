module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.NT44.NormalizerLayer
import CFSG.GH74.GLS.NT44.IntrinsicCore
import CFSG.GH74.GLS.NT44.ProductLayer
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.GH74.GLS.NT44.RigidCenterSylow
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers
import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsConstraint
import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQuaternion
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
public import CFSG.GH74.GLS.Stage2.Local.Defs

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem le_layerCore_normalizer_of_le_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {W Y : Subgroup G}
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hx2 : orderOf x = 2)
    (hmax : ∀ a : G, orderOf a = 2 →
      (RigidSet fullQ a).ncard ≤ (RigidSet fullQ x).ncard)
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x)))
    (hYW : Y ≤ W)
    (hYne : Y ≠ ⊥) :
    W ≤ ((CFSG.Op_p'p 2 ↥(CFSG.pLayer ↥(Subgroup.normalizer (Y : Set G)) 2)).map
      (CFSG.pLayer ↥(Subgroup.normalizer (Y : Set G)) 2).subtype).map
      (Subgroup.normalizer (Y : Set G)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := Kz fullQ x
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  let E : Subgroup G := (CFSG.pLayer ↥N 2).map N.subtype
  have hW2 : IsPGroup 2 W := hW.isPGroup
  have hWz : W ≤ zStar P := by simpa [P] using hW.le
  have hWE : W ≤ E := by
    simpa [E, N] using
      (CFSG.GH74.GLS.NT44.le_pLayer_normalizer_of_le_zStar_kz
        (G := G) (fullQ := fullQ) (x := x) (W := W) (Y := Y)
        hx2 hW2 (by simpa [P] using hWz) hYW)
  have hY2 : IsPGroup 2 Y := hW2.to_le hYW
  obtain ⟨y, hyY, hy2⟩ :=
    CFSG.ABGLocalTools.exists_mem_orderOf_eq_two (X := Y) hY2 hYne
  have hyW : y ∈ W := hYW hyY
  let R : Subgroup G := Kz fullQ y
  let Cy : Subgroup G := Subgroup.centralizer ({y} : Set G)
  let F : Subgroup G := (CFSG.pLayer ↥Cy 2).map Cy.subtype
  have hO22_op : ∀ U : Subgroup G,
      CFSG.GH74.GLS.Stage2.Local.O22Of U =
        (CFSG.Op_p'p 2 ↥U).map U.subtype := by
    intro U
    simp only [CFSG.GH74.GLS.Stage2.Local.O22Of, CFSG.GH74.GLS.pPrimePCore,
      CFSG.Op_p'p]
  have hO22_subgroupOf : ∀ (U V : Subgroup G) (hUV : U ≤ V),
      ((CFSG.Op_p'p 2 ↥(U.subgroupOf V)).map (U.subgroupOf V).subtype).map V.subtype =
        CFSG.GH74.GLS.Stage2.Local.O22Of U := by
    intro U V hUV
    have hmap : (U.subgroupOf V).map V.subtype = U :=
      Subgroup.map_subgroupOf_eq_of_le hUV
    have hO := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.O22Of_map
      (G' := ↥V) (G := G) (f := V.subtype) V.subtype_injective (U.subgroupOf V)
    rw [hmap] at hO
    simpa only [CFSG.GH74.GLS.Stage2.Local.O22Of, CFSG.GH74.GLS.pPrimePCore,
      CFSG.Op_p'p] using hO.symm
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    exact CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := W) (K := P)
      hW2 ha hb (hWz ha).1 (hWz hb).2
  have hyP : y ∈ P := (hWz hyW).1
  have hyCx : y ∈ Subgroup.centralizer ({x} : Set G) :=
    (CFSG.GH74.GLS.NT44.kz_le_centralizer (Q := fullQ) (z := x)) (by
      simpa [P] using hyP)
  have hxCy : x ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCx).symm
  obtain ⟨J, hJ⟩ :=
    CFSG.GH74.GLS.NT44.exists_pump_family_of_mem_zStar_kz
      (G := G) (fullQ := fullQ) (x := x) (t := y)
      hnonab hy2 (by simpa [P] using hWz hyW)
  have hcov :=
    CFSG.GH74.GLS.NT44.rigid_product_coverage
      (G := G) (fullQ := fullQ) (x := x) (t := y)
      J hxCy hJ (hmax y hy2)
  have hWR : W ≤ zStar R := by
    have hSylow := CFSG.GH74.GLS.NT44.isSylowOf_zStar_kz_of_coverage
      (G := G) (fullQ := fullQ) (x := x) (t := y) (W := W)
      hW hyW hcov.1 hcov.2
    simpa [R] using hSylow.le
  have hWKR_op : W ≤ (CFSG.Op_p'p 2 ↥R).map R.subtype := by
    simpa [R] using
      (CFSG.GH74.GLS.NT44.le_Op_p'p_of_le_zStar
        (G := G) (W := W) (R := R) hW2 hWR)
  have hWKR_O : W ≤ CFSG.GH74.GLS.Stage2.Local.O22Of R := by
    rw [hO22_op R]
    exact hWKR_op
  have hRCy : R ≤ Cy := by
    simpa [R, Cy] using
      (CFSG.GH74.GLS.NT44.kz_le_centralizer (Q := fullQ) (z := y))
  have hCyNR : Cy ≤ Subgroup.normalizer (R : Set G) := by
    simpa [R, Cy] using
      (CFSG.GH74.GLS.NT44.centralizer_le_normalizer_kz (Q := fullQ) (z := y))
  have hRnormCy : (R.subgroupOf Cy).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRCy).mpr hCyNR
  have htopR : CFSG.pLayer ↥R 2 = ⊤ := by
    simpa [R] using
      (CFSG.GH74.GLS.NT44.pLayer_kz_eq_top_and_kBar
        (G := G) (fullQ := fullQ) y).1
  have hRF : R ≤ F := by
    have hmono := CFSG.ComponentClassification.GrSLit.pLayer_map_le_of_isSubnormal
      (G := G) (N := R) (H := Cy) hRCy hRnormCy.isSubnormal
    have hRle : R ≤ (CFSG.pLayer ↥R 2).map R.subtype := by
      rw [htopR]
      intro r hr
      exact Subgroup.mem_map.mpr ⟨⟨r, hr⟩, Subgroup.mem_top _, rfl⟩
    exact hRle.trans (by simpa [F] using hmono)
  have hFNR : F ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.map_subtype_le (CFSG.pLayer ↥Cy 2)).trans hCyNR
  have hRnormF : (R.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRF).mpr hFNR
  have hKF_O : CFSG.GH74.GLS.Stage2.Local.O22Of R ≤
      CFSG.GH74.GLS.Stage2.Local.O22Of F := by
    have : (R.subgroupOf F).Normal := hRnormF
    have hUp : (CFSG.Op_p'p 2 ↥(R.subgroupOf F)).map (R.subgroupOf F).subtype ≤
        CFSG.Op_p'p 2 ↥F :=
      CFSG.Wreathed.OriginalAllPrime.map_Op_p'p_le_of_normal 2 (R.subgroupOf F)
    have hUpMap := Subgroup.map_mono (f := F.subtype) hUp
    rw [← hO22_subgroupOf R F hRF, hO22_op F]
    exact hUpMap
  have hWKF_O : W ≤ CFSG.GH74.GLS.Stage2.Local.O22Of F := hWKR_O.trans hKF_O
  have hYCy : Y ≤ Cy := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z (hYW hz) y hyW)
  have hHleCy : Subgroup.centralizer (Y : Set G) ≤ Cy := by
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hh) y hyY).symm
  have hEN : E ≤ (CFSG.pLayer ↥(Subgroup.centralizer (Y : Set G)) 2).map
      (Subgroup.centralizer (Y : Set G)).subtype := by
    have hbal := CFSG.ComponentClassification.LBalance.lBalancePLayer_normalizer_le_centralizer
      (X := G) (p := 2) Y hY2
    rw [CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map (p := 2),
      CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map (p := 2)] at hbal
    simpa [E, N] using hbal
  have hYbal : (CFSG.pLayer ↥(Subgroup.centralizer (Y : Set G)) 2).map
      (Subgroup.centralizer (Y : Set G)).subtype ≤ F := by
    have hbal := CFSG.ComponentClassification.GrSLit.pLayer_inf_centralizer_le
      (G := G) (Y := Cy) (A := Y) hYCy hY2
    have hCyH : Cy ⊓ Subgroup.centralizer (Y : Set G) =
        Subgroup.centralizer (Y : Set G) :=
      inf_eq_right.mpr hHleCy
    rw [hCyH] at hbal
    simpa [F] using hbal
  have hEF : E ≤ F := hEN.trans hYbal
  let A : Subgroup ↥F := E.subgroupOf F
  have hdown : (CFSG.Op_p'p 2 ↥F).subgroupOf A ≤ CFSG.Op_p'p 2 ↥A :=
    CFSG.Wreathed.OriginalAllPrime.Op_p'p_subgroupOf_le 2 A
  have hWKE : W ≤ CFSG.GH74.GLS.Stage2.Local.O22Of E := by
    intro w hw
    have hwE : w ∈ E := hWE hw
    have hwKF : w ∈ (CFSG.Op_p'p 2 ↥F).map F.subtype := by
      have h := hWKF_O hw
      rwa [hO22_op F] at h
    obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hwKF
    have hvE : (v : G) ∈ E := by
      change F.subtype v ∈ E
      rw [hvw]
      exact hwE
    have hvA : v ∈ E.subgroupOf F := by
      rw [Subgroup.mem_subgroupOf]
      exact hvE
    let a : A := ⟨v, hvA⟩
    have ha : a ∈ (CFSG.Op_p'p 2 ↥F).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hv
    have haCore : a ∈ CFSG.Op_p'p 2 ↥A := hdown ha
    have hmapA : (a : F) ∈ (CFSG.Op_p'p 2 ↥A).map A.subtype :=
      Subgroup.mem_map.mpr ⟨a, haCore, rfl⟩
    have hmapF : ((a : F) : G) ∈
        ((CFSG.Op_p'p 2 ↥A).map A.subtype).map F.subtype :=
      Subgroup.mem_map.mpr ⟨(a : F), hmapA, rfl⟩
    have haw : ((a : F) : G) = w := by
      change (v : G) = w
      exact hvw
    rw [haw] at hmapF
    rw [← hO22_subgroupOf E F hEF]
    simpa [A] using hmapF
  have hO22E : CFSG.GH74.GLS.Stage2.Local.O22Of
      ((CFSG.pLayer ↥N 2).map N.subtype) =
      (CFSG.GH74.GLS.Stage2.Local.O22Of (CFSG.pLayer ↥N 2)).map N.subtype :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.O22Of_map
      N.subtype_injective (CFSG.pLayer ↥N 2)
  have hO22E' : CFSG.GH74.GLS.Stage2.Local.O22Of E =
      (CFSG.GH74.GLS.Stage2.Local.O22Of (CFSG.pLayer ↥N 2)).map N.subtype := by
    simpa [E] using hO22E
  have hO22N : (CFSG.GH74.GLS.Stage2.Local.O22Of (CFSG.pLayer ↥N 2)).map N.subtype =
      ((CFSG.Op_p'p 2 ↥(CFSG.pLayer ↥N 2)).map
        (CFSG.pLayer ↥N 2).subtype).map N.subtype := by
    simp only [CFSG.GH74.GLS.Stage2.Local.O22Of, CFSG.GH74.GLS.pPrimePCore,
      CFSG.Op_p'p]
  have h2 : W ≤ (CFSG.GH74.GLS.Stage2.Local.O22Of (CFSG.pLayer ↥N 2)).map
      N.subtype := by
    rwa [hO22E'] at hWKE
  rw [hO22N] at h2
  simpa [N] using h2

end CFSG.GH74.GLS.NT44

end
