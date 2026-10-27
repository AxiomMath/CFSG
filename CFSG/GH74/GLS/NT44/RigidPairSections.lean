module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.GH74.GLS.Bg.Pu5.L296Basic
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
import CFSG.GH74.Generic.BProg.B3.S3T3E8B
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBTwoFactorImage
import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.GH74.GLS.TwoThin.PumpData

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
open scoped Pointwise

private theorem isPCompIn_kz_of_mem_rigidSet
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x) :
    IsPCompIn 2 (Kz fullQ x) J := by
  exact Bg.Pu5.isPCompIn_of_le' hJ.1.1.2.2 (le_sSup hJ)
    (NT44.kz_le_centralizer (Q := fullQ))

private theorem mem_centralizerSection_of_mem_wholeProductSection
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x a : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x)
    (ha : a ∈ centralizerSection (Kz fullQ x) (pPrimeCoreOf 2 (Kz fullQ x))) :
    a ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  exact CFSG.OddStandard.Solomon75.normalizes_isPCompIn_of_comm_mem
    (isPCompIn_kz_of_mem_rigidSet hJ) ha.1 (fun j hj => ha.2.2 j (le_sSup hJ hj))

private theorem mem_centralizerSection_of_le_centralizer
    {G : Type} [Group G] {x : G} {J : Subgroup G}
    (hJ : J ≤ centralizer ({x} : Set G)) :
    x ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  exact C3.Layer1.Back.mem_centralizerSection_of_centralizes
    (fun j hj => (mem_centralizer_singleton_iff.mp (hJ hj)).symm)
    (Subgroup.map_subtype_le _)

private theorem pRank_three_at_actual_w
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x v w : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hw2 : orderOf w = 2) (hwC : w ∈ centralizer ({x, v} : Set G))
    (hwP : w ∈ centralizerSection (Kz fullQ x) (pPrimeCoreOf 2 (Kz fullQ x))) :
    3 ≤ pRank 2 ↥(centralizer ({w} : Set G)) := by
  have hx2 : orderOf x = 2 := hJ.1.1.1
  have hv2 : orderOf v = 2 := hxv.orderOf_eq.symm.trans hx2
  by_cases hwx : w = x
  · subst w
    simpa [oBound] using hJ.1.1.2.1
  · have hx1 : x ≠ 1 := by intro h; simp [h] at hx2
    have hw1 : w ≠ 1 := by intro h; simp [h] at hw2
    have hwJ := mem_centralizerSection_of_mem_wholeProductSection hJ hwP
    have hxJ := mem_centralizerSection_of_le_centralizer hJ.1.1.2.2.1
    have hE0 : zpowers x ⊔ zpowers w ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
      sup_le (zpowers_le.mpr hxJ) (zpowers_le.mpr hwJ)
    have hvE0 : v ∉ zpowers x ⊔ zpowers w := fun hv => hvact (hE0 hv)
    have hwE : w ∉ zpowers x := by
      intro hw
      rcases (CFSG.ComponentClassification.UnbalancedGS.mem_zpowers_iff_eq_one_or_eq hx2).mp hw with h | h
      · exact hw1 h
      · exact hwx h
    have hwCx : w ∈ centralizer ({x} : Set G) := centralizer_le (by simp) hwC
    have hwCv : w ∈ centralizer ({v} : Set G) := centralizer_le (by simp) hwC
    have hxw : x * w = w * x := (mem_centralizer_singleton_iff.mp hwCx).symm
    have hwv : w * v = v * w := mem_centralizer_singleton_iff.mp hwCv
    have hxx : x * x = 1 := by simpa only [hx2, pow_two] using pow_orderOf_eq_one x
    have hww : w * w = 1 := by simpa only [hw2, pow_two] using pow_orderOf_eq_one w
    have hvv : v * v = 1 := by simpa only [hv2, pow_two] using pow_orderOf_eq_one v
    obtain ⟨hE, hcard⟩ := CFSG.GH74.Generic.BProg.B3.S3T3.e8_of_triple
      hxx hx1 hww hvv hxw hvx.symm hwv hwE hvE0
    let E : Subgroup G := zpowers x ⊔ zpowers w ⊔ zpowers v
    have hEC : E ≤ centralizer ({w} : Set G) :=
      sup_le (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxw))
        (zpowers_le.mpr (by simp [mem_centralizer_singleton_iff])))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwv.symm))
    let : CFSG.IsElementaryAbelian 2 ↥E := hE
    have hErank : pRank 2 ↥E = 3 := CFSG.pRank_eq_of_card_eq_pow one_lt_two
      (by simpa [E] using hcard)
    rw [← hErank]
    exact C3.Layer1.Back.pRank_mono' hEC

private theorem exists_pumpupAssignment_at_actual_w
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {s w : G} (hw2 : orderOf w = 2)
    (hwCs : w ∈ centralizer ({s} : Set G))
    (hwP : w ∈ centralizerSection (Kz fullQ s) (pPrimeCoreOf 2 (Kz fullQ s)))
    (hR : 3 ≤ pRank 2 ↥(centralizer ({w} : Set G))) :
    ∃ F : Subgroup G → Subgroup G,
      ∀ K ∈ RigidSet fullQ s, PumpUpLT 2 s K w (F K) := by
  classical
  have hex : ∀ K : Subgroup G, ∃ M : Subgroup G,
      K ∈ RigidSet fullQ s → PumpUpLT 2 s K w M := by
    intro K
    by_cases hK : K ∈ RigidSet fullQ s
    · obtain ⟨M, hM⟩ := TwoThin.exists_pumpup_of_involution hK.1.1.1 hw2 hK.1.1.2.2
        hwCs (mem_centralizerSection_of_mem_wholeProductSection hK hwP) hK.1.1 hR
      exact ⟨M, fun _ => hM⟩
    · exact ⟨⊥, fun h => False.elim (hK h)⟩
  choose F hF using hex
  exact ⟨F, hF⟩

private theorem ncard_rigidSet_le_at_actual_w
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x v w : G} (hxv : IsConj x v) (hw2 : orderOf w = 2)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x)) :
    (RigidSet fullQ w).ncard ≤ (RigidSet fullQ x).ncard ∧
      (RigidSet fullQ w).ncard ≤ (RigidSet fullQ v).ncard := by
  have hwx : (RigidSet fullQ w).ncard ≤ (RigidSet fullQ x).ncard := by
    simpa only [Nat.card_coe_set_eq] using hmax w hw2
  have hvEq : (RigidSet fullQ v).ncard = (RigidSet fullQ x).ncard := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxv
    simpa only [hg] using NT44.ncard_rigidSet_conj (Q := fullQ) (z := x) g
  exact ⟨hwx, by simpa only [hvEq] using hwx⟩

private theorem wholeProduct_covers_at_actual_w
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x v w : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (hw2 : orderOf w = 2) (hwC : w ∈ centralizer ({x, v} : Set G))
    (hwPx : w ∈ centralizerSection (Kz fullQ x) (pPrimeCoreOf 2 (Kz fullQ x)))
    (hwPv : w ∈ centralizerSection (Kz fullQ v) (pPrimeCoreOf 2 (Kz fullQ v))) :
    ((Kz fullQ x ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ x) = Kz fullQ x) ∧
    ((Kz fullQ x ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ w) = Kz fullQ w) ∧
    ((Kz fullQ v ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ v) = Kz fullQ v) ∧
    ((Kz fullQ v ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ w) = Kz fullQ w) := by
  have hR := pRank_three_at_actual_w hJ hxv hvx hvact hw2 hwC hwPx
  have hwCx : w ∈ centralizer ({x} : Set G) := centralizer_le (by simp) hwC
  have hwCv : w ∈ centralizer ({v} : Set G) := centralizer_le (by simp) hwC
  obtain ⟨Fx, hFx⟩ := exists_pumpupAssignment_at_actual_w hw2 hwCx hwPx hR
  obtain ⟨Fv, hFv⟩ := exists_pumpupAssignment_at_actual_w hw2 hwCv hwPv hR
  obtain ⟨hxmax, hvmax⟩ := ncard_rigidSet_le_at_actual_w hxv hw2 hmax
  have hxcover := NT44.rigid_product_coverage Fx (TwoThin.mem_centralizer_symm hwCx) hFx hxmax
  have hvcover := NT44.rigid_product_coverage Fv (TwoThin.mem_centralizer_symm hwCv) hFv hvmax
  exact ⟨hxcover.1, hxcover.2, hvcover.1, hvcover.2⟩

private theorem cover_mul_decomposition {G : Type} [Group G] [Finite G]
    {D B : Subgroup G} (hDB : D ≤ B) (hcover : D ⊔ pPrimeCoreOf 2 B = B) :
    ∀ b ∈ B, ∃ d ∈ D, ∃ o ∈ pPrimeCoreOf 2 B, b = d * o := by
  have hDN : D ≤ normalizer (pPrimeCoreOf 2 B : Set G) :=
    hDB.trans (le_normalizer.trans
      (CFSG.OddStandard.Solomon75.normalizer_le_normalizer_pPrimeCoreOf B))
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right D (pPrimeCoreOf 2 B) hDN
  rw [hcover] at hset
  intro b hb
  have hbprod : b ∈ (D : Set G) * (pPrimeCoreOf 2 B : Set G) := by
    rw [← hset]
    exact hb
  obtain ⟨d, hd, o, ho, heq⟩ := hbprod
  exact ⟨d, hd, o, ho, heq.symm⟩

private theorem mem_centralizerSection_original_of_actual_covers
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ]
    {x v w : G} {J : Subgroup G} (hJ : J ∈ RigidSet fullQ x)
    (hvx : v * x = x * v) (hwC : w ∈ centralizer ({x, v} : Set G))
    (hx : (Kz fullQ x ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ x) = Kz fullQ x)
    (hxw : (Kz fullQ x ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ w) = Kz fullQ w)
    (hv : (Kz fullQ v ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ v) = Kz fullQ v)
    (hvw : (Kz fullQ v ⊓ Kz fullQ w) ⊔ pPrimeCoreOf 2 (Kz fullQ w) = Kz fullQ w) :
    v ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have hvCx : v ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hvx
  have hvCv : v ∈ centralizer ({v} : Set G) := by simp [mem_centralizer_singleton_iff]
  have hwCv : w ∈ centralizer ({v} : Set G) := centralizer_le (by simp) hwC
  have hvCw : v ∈ centralizer ({w} : Set G) := TwoThin.mem_centralizer_symm hwCv
  have hnPx := NT44.centralizer_le_normalizer_kz (Q := fullQ) hvCx
  have hnPv := NT44.centralizer_le_normalizer_kz (Q := fullQ) hvCv
  have hnPw := NT44.centralizer_le_normalizer_kz (Q := fullQ) hvCw
  have hnDx := TwoThin.mem_normalizer_inf hnPx hnPw
  have hnDv := TwoThin.mem_normalizer_inf hnPv hnPw
  have hvSecPv := mem_centralizerSection_of_le_centralizer
    (NT44.kz_le_centralizer (Q := fullQ) (z := v))
  have hvSecDv := Bg.Iii2.L41.mem_cSec_of_cover inf_le_left
    (cover_mul_decomposition inf_le_left hv) hnDv hvSecPv
  have hvSecPw := Bg.Iii2.L41.mem_cSec_of_cover' inf_le_right
    (cover_mul_decomposition inf_le_right hvw) hnPw hvSecDv
  have hvSecDx := Bg.Iii2.L41.mem_cSec_of_cover inf_le_right
    (cover_mul_decomposition inf_le_right hxw) hnDx hvSecPw
  have hvSecPx := Bg.Iii2.L41.mem_cSec_of_cover' inf_le_left
    (cover_mul_decomposition inf_le_left hx) hnPx hvSecDx
  exact mem_centralizerSection_of_mem_wholeProductSection hJ hvSecPx

theorem not_exists_involution_mem_centralizer_pair_sections_of_rigid_actor
    {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ]
    {x v : G} {J : Subgroup G}
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hxv : IsConj x v) (hvx : v * x = x * v)
    (hvact : v ∉ CFSG.GH74.GLS.centralizerSection J (CFSG.GH74.GLS.pPrimeCoreOf 2 J))
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ s) ≤
        Nat.card ↥(CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)) :
    ¬ ∃ w : G, orderOf w = 2 ∧
      w ∈ Subgroup.centralizer ({x, v} : Set G) ∧
      w ∈ CFSG.GH74.GLS.centralizerSection
        (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)
        (CFSG.GH74.GLS.pPrimeCoreOf 2 (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)) ∧
      w ∈ CFSG.GH74.GLS.centralizerSection
        (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ v)
        (CFSG.GH74.GLS.pPrimeCoreOf 2 (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ v)) := by
  rintro ⟨w, hw2, hwC, hwPx, hwPv⟩
  obtain ⟨hx, hxw, hv, hvw⟩ :=
    wholeProduct_covers_at_actual_w hJ hxv hvx hvact hmax hw2 hwC hwPx hwPv
  exact hvact (mem_centralizerSection_original_of_actual_covers hJ hvx hwC hx hxw hv hvw)

end CFSG.GH74.GLS.NT44

end
