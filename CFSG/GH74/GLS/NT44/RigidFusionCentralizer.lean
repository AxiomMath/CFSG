module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.GH74.GLS.NT44.RigidFusionForward

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS.Stage1.Thm4

theorem mem_zStar_kz_of_isConj_of_mem_cSec_of_even
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x y : G} {K : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hEven : Even (Nat.card (Subgroup.center fullQ)))
    (hxZ : x ∈ zStar (Kz fullQ x))
    (hmax : ∀ a : G, orderOf a = 2 →
      (RigidSet fullQ a).ncard ≤ (RigidSet fullQ x).ncard)
    (hyC : y ∈ Subgroup.centralizer ({x} : Set G))
    (hconj : IsConj x y)
    (hysec : y ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    y ∈ zStar (Kz fullQ x) := by
  classical
  have hx2 : orderOf x = 2 := hK.1.1.1
  have hy2 : orderOf y = 2 := by
    rw [← hconj.orderOf_eq, hx2]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf (G := G) 2
      (Subgroup.centralizer ({x} : Set G))
  obtain ⟨c, hc, hy'T⟩ :=
    CFSG.GH74.GLS.Bg.Pu5.exists_conj_mem_of_isSylowOf'
      (K := Subgroup.centralizer ({x} : Set G)) hT hyC ⟨1, by simpa using hy2⟩
  let y' : G := c * y * c⁻¹
  let K' : Subgroup G := CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap c K
  have hy'T' : y' ∈ T := hy'T
  have hK' : IsRigidOfType fullQ x K' := by
    have hcx : c * x * c⁻¹ = x :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec4.conj_fix_of_mem_centralizer hc
    have h := isRigidOfType_conj (Q := fullQ)
      (show IsRigidOfType fullQ x K from hK) c
    rwa [hcx] at h
  have hconj' : IsConj x y' :=
    hconj.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hysec' : y' ∈ centralizerSection K' (pPrimeCoreOf 2 K') := by
    simpa only [K', y', CFSG.GH74.GLS.Stage1.Thm2.Recip.cSec] using
      CFSG.GH74.GLS.Bg.Pu5.conj_mem_cSec_cmap (K := K) (x := y) hysec c
  have hy'Z : y' ∈ zStar (Kz fullQ x) :=
    (mem_inf_zStar_kz_of_isConj_of_mem_cSec_of_even
      (G := G) (fullQ := fullQ)
      hK' hT hEven hxZ hmax hy'T' hconj' hysec').2
  have hc_inv : c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
    (Subgroup.centralizer ({x} : Set G)).inv_mem hc
  have hcnorm : c⁻¹ ∈ Subgroup.normalizer (Kz fullQ x : Set G) :=
    (centralizer_le_normalizer_kz (Q := fullQ) (z := x)) hc_inv
  have hback : c⁻¹ * y' * (c⁻¹)⁻¹ ∈ zStar (Kz fullQ x) :=
    CFSG.GH74.GLS.Stage1.Thm4.Alt51.zStar_conj (K := Kz fullQ x) hcnorm hy'Z
  have hEq : c⁻¹ * y' * (c⁻¹)⁻¹ = y := by
    simp only [y', inv_inv]
    group
  rwa [hEq] at hback

end CFSG.GH74.GLS.NT44

end
