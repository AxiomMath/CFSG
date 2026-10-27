module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs

import CFSG.GH74.GLS.NT44.RigidFusionCentralizer
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.NoncentralInvolution
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport
import CFSG.GH74.GLS.NT44.OriginalSylowActor
import CFSG.GH74.GLS.NT44.IntrinsicCore
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.GLS.TwoThin.ClassCongr
import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

set_option autoImplicit false

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4
open CFSG.GH74.GLS.Bg.Pu5

namespace CFSG.GH74.GLS.NT44

theorem exists_conjugate_normalizing_not_mem_cSec_of_not_closure_le_zStar_of_even
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {K T : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hT : ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (hL34 : IsL34Quotient fullQ)
    (hEven : Even (Nat.card (Subgroup.center fullQ)))
    (hxZ : x ∈ zStar (Kz fullQ x))
    (hmax : ∀ a : G, orderOf a = 2 →
      (RigidSet fullQ a).ncard ≤ (RigidSet fullQ x).ncard)
    (hBnot : ¬ (Subgroup.closure {y : G | y ∈ T ∧ IsConj x y} ≤
      zStar (Kz fullQ x))) :
    ∃ v : G, v ∈ T ∧ IsConj x v ∧ orderOf v = 2 ∧
      v ∈ Subgroup.normalizer (K : Set G) ∧
      v ∉ centralizerSection K (pPrimeCoreOf 2 K) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let P : Subgroup G := Kz fullQ x
  have hx2 : orderOf x = 2 := hK.1.1.1
  have hKcomp : IsPCompIn 2 C K := hK.1.1.2.2
  have hy_exists : ∃ y : G, y ∈ T ∧ IsConj x y ∧ y ∉ zStar P := by
    by_contra h
    apply hBnot
    rw [Subgroup.closure_le]
    intro y hy
    by_contra hyZ
    exact h ⟨y, hy.1, hy.2, by simpa [P] using hyZ⟩
  obtain ⟨y, hyT, hconj, hyZ⟩ := hy_exists
  have hyC : y ∈ C := CFSG.ABGLocalTools.IsSylowOf.le hT hyT
  have hyZ' : y ∉ zStar (Kz fullQ x) := by simpa [P] using hyZ
  by_cases hyN : y ∈ Subgroup.normalizer (K : Set G)
  · refine ⟨y, hyT, hconj, ?_, hyN, ?_⟩
    · rw [← hconj.orderOf_eq, hx2]
    · intro hysec
      exact hyZ' (mem_zStar_kz_of_isConj_of_mem_cSec_of_even
        (G := G) (fullQ := fullQ) hK hEven hxZ hmax hyC hconj hysec)
  · have hP' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
      P92.sylow_inf hK hT
    let e : kBar K ≃* fullQ := hK.2.some
    have hL34K : IsL34Quotient (kBar K) :=
      CFSG.GH74.GLS.TwoThin.isL34Quotient_of_mulEquiv e.symm hL34
    obtain ⟨u, huP', hu2, huZ⟩ :=
      exists_involution_mem_sylow_not_mem_zStar_of_isL34Quotient K (T ⊓ K) hP' hL34K
    have huT : u ∈ T := (Subgroup.mem_inf.mp huP').1
    have huK : u ∈ K := (Subgroup.mem_inf.mp huP').2
    obtain ⟨v, hvT, hvconj, hv2, hvN, hvnotO22⟩ :=
      exists_conjugate_mem_sylow_normalizing_not_mem_core
        (G := G) (x := x) (y := y) (u := u) (K := K) (T := T)
        hKcomp hx2 hT hyT hconj huT huK hu2 huZ hyN
    refine ⟨v, hvT, hvconj, hv2, hvN, ?_⟩
    intro hvsec
    have hvC : v ∈ C := CFSG.ABGLocalTools.IsSylowOf.le hT hvT
    have hvZ : v ∈ zStar P := by
      simpa [P] using mem_zStar_kz_of_isConj_of_mem_cSec_of_even
        (G := G) (fullQ := fullQ) hK hEven hxZ hmax hvC hvconj hvsec
    have hW2 : IsPGroup 2 (Subgroup.zpowers v) :=
      isPGroup_zpowers_of_pow_eq_one (exists_two_pow_eq_one_of_orderOf hv2)
    have hWZ : Subgroup.zpowers v ≤ zStar P := Subgroup.zpowers_le.mpr hvZ
    have hWOp : Subgroup.zpowers v ≤ (CFSG.Op_p'p 2 ↥P).map P.subtype :=
      le_Op_p'p_of_le_zStar hW2 hWZ
    have hvCore : v ∈ (CFSG.Op_p'p 2 ↥P).map P.subtype :=
      hWOp (Subgroup.mem_zpowers v)
    let A : Subgroup C := P.subgroupOf C
    have hPC : P ≤ C := kz_le_centralizer (Q := fullQ) (z := x)
    have hCN : C ≤ Subgroup.normalizer (P : Set G) :=
      centralizer_le_normalizer_kz (Q := fullQ) (z := x)
    have hA_map : A.map C.subtype = P := by
      dsimp [A]
      exact Subgroup.map_subgroupOf_eq_of_le hPC
    have hA_normal : A.Normal := by
      dsimp [A]
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPC]
      exact hCN
    have hA_normal' : A.Normal := hA_normal
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmap_le : (CFSG.Op_p'p 2 ↥A).map A.subtype ≤ CFSG.Op_p'p 2 ↥C := by
      let : A.Normal := hA_normal'
      let : Fact (Nat.Prime 2) := hfact
      exact CFSG.Wreathed.OriginalAllPrime.map_Op_p'p_le_of_normal
        (p := 2) (H := ↥C) (A := A)
    have hO22_eq : (CFSG.Op_p'p 2 ↥P).map P.subtype =
        ((CFSG.Op_p'p 2 ↥A).map A.subtype).map C.subtype := by
      change CFSG.GH74.GLS.Stage2.Local.O22Of P =
        (CFSG.GH74.GLS.Stage2.Local.O22Of A).map C.subtype
      rw [← hA_map]
      exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.O22Of_map
        C.subtype_injective A
    have hvSmall : v ∈ ((CFSG.Op_p'p 2 ↥A).map A.subtype).map C.subtype := by
      rw [← hO22_eq]
      exact hvCore
    have hmap_le' : ((CFSG.Op_p'p 2 ↥A).map A.subtype).map C.subtype ≤
        (CFSG.Op_p'p 2 ↥C).map C.subtype :=
      Subgroup.map_mono (f := C.subtype) hmap_le
    have hvO22C : v ∈ (CFSG.Op_p'p 2 ↥C).map C.subtype := hmap_le' hvSmall
    have hvO22 : v ∈ CFSG.GH74.GLS.Stage1.Thm2.Recip.O22 C := by
      change v ∈ (CFSG.Op_p'p 2 ↥C).map C.subtype
      exact hvO22C
    exact hvnotO22 (by simpa [C] using hvO22)

theorem exists_conjugate_normalizing_not_mem_cSec_of_not_closure_le_zStar
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {K T : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hT : ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (hL34 : IsL34Quotient fullQ)
    (h16 : Nat.card (Subgroup.center fullQ) = 16)
    (hxZ : x ∈ zStar (Kz fullQ x))
    (hmax : ∀ a : G, orderOf a = 2 →
      (RigidSet fullQ a).ncard ≤ (RigidSet fullQ x).ncard)
    (hBnot : ¬ (Subgroup.closure {y : G | y ∈ T ∧ IsConj x y} ≤
      zStar (Kz fullQ x))) :
    ∃ v : G, v ∈ T ∧ IsConj x v ∧ orderOf v = 2 ∧
      v ∈ Subgroup.normalizer (K : Set G) ∧
      v ∉ centralizerSection K (pPrimeCoreOf 2 K) := by
  have hEven : Even (Nat.card (Subgroup.center fullQ)) := by
    rw [h16]
    norm_num
  exact exists_conjugate_normalizing_not_mem_cSec_of_not_closure_le_zStar_of_even
    hK hT hL34 hEven hxZ hmax hBnot

end CFSG.GH74.GLS.NT44

end
