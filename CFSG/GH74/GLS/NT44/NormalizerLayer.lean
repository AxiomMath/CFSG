module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.NT44.ProductLayer
import CFSG.GH74.GLS.NT44.FixedLayer
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

theorem le_pLayer_normalizer_of_le_zStar_kz
    {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ]
    {x : G} {W Y : Subgroup G}
    (hx2 : orderOf x = 2)
    (hW2 : IsPGroup 2 W)
    (hWZ : W ≤ zStar (Kz fullQ x))
    (hYW : Y ≤ W) :
    W ≤ (CFSG.pLayer ↥(Subgroup.normalizer (Y : Set G)) 2).map
      (Subgroup.normalizer (Y : Set G)).subtype := by
  let P : Subgroup G := CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let H : Subgroup G := Subgroup.centralizer (Y : Set G)
  let D : Subgroup G := Cx ⊓ H
  have hPtop : CFSG.pLayer (CFSG.GH74.GLS.kBar P) 2 = ⊤ :=
    (pLayer_kz_eq_top_and_kBar (G := G) (fullQ := fullQ) x).2
  have hWZ' : W ≤ CFSG.GH74.GLS.zStar P := hWZ
  have hPCx : P ≤ Cx := kz_le_centralizer (Q := fullQ) (z := x)
  have hCxN : Cx ≤ Subgroup.normalizer (P : Set G) :=
    centralizer_le_normalizer_kz (Q := fullQ) (z := x)
  have hFixed : W ≤ (CFSG.pLayer ↥(P ⊓ H) 2).map (P ⊓ H).subtype :=
    le_pLayer_inf_centralizer_of_le_zStar (P := P) (W := W) (Y := Y)
      hPtop hW2 hWZ' hYW
  have hPD : P ⊓ H ≤ D := inf_le_inf_right H hPCx
  have hnorm : ((P ⊓ H).subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPD]
    intro n d hn hd
    obtain ⟨hnP, hnH⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨hdCx, hdH⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hCxN hdCx) n).mp hnP
    · exact H.mul_mem (H.mul_mem hdH hnH) (H.inv_mem hdH)
  have hPDlayer : (CFSG.pLayer ↥(P ⊓ H) 2).map (P ⊓ H).subtype ≤
      (CFSG.pLayer ↥D 2).map D.subtype :=
    CFSG.ComponentClassification.GrSLit.pLayer_map_le_of_isSubnormal hPD hnorm.isSubnormal
  have hxH : x ∈ H := by
    change x ∈ Subgroup.centralizer (Y : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y ∈ P := (hWZ' (hYW hy)).1
    have hyCx : y ∈ Cx := hPCx hyP
    exact ((Subgroup.mem_centralizer_iff.mp hyCx) x (Set.mem_singleton x)).symm
  have hzp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hCxzp : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hHbal := CFSG.ComponentClassification.GrSLit.pLayer_inf_centralizer_le
    (Y := H) (A := Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxH) hzp
  have hDlayer : (CFSG.pLayer ↥D 2).map D.subtype ≤
      (CFSG.pLayer ↥H 2).map H.subtype := by
    have hEq : H ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) = D := by
      rw [hCxzp]
      exact inf_comm H Cx
    rwa [hEq] at hHbal
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.centralizer_le_normalizer (Y : Set G)
  have hHnorm : (H.subgroupOf (Subgroup.normalizer (Y : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (Y : Set G)
  have hHlayer : (CFSG.pLayer ↥H 2).map H.subtype ≤
      (CFSG.pLayer ↥(Subgroup.normalizer (Y : Set G)) 2).map
        (Subgroup.normalizer (Y : Set G)).subtype :=
    CFSG.ComponentClassification.GrSLit.pLayer_map_le_of_isSubnormal hHN hHnorm.isSubnormal
  exact hFixed.trans (hPDlayer.trans (hDlayer.trans hHlayer))

end CFSG.GH74.GLS.NT44

end
