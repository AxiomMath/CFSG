module

import CFSG.GH74.GLS.NT44.FieldFixedLayer
import CFSG.GH74.GLS.NT44.SquareTransfer
import CFSG.GH74.GLS.NT44.RigidFamily
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import TauCeti.GroupTheory.QuotientGroup.MulAut

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm4

theorem false_of_rigid_actor_of_not_inner_conj
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {fullQ : Type} [Group fullQ]
    (hL34 : IsL34Quotient fullQ) (h16 : Nat.card (Subgroup.center fullQ) = 16)
    {x v : G} {J : Subgroup G}
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2) (hxv : IsConj x v) (hvx : v * x = x * v)
    (hJ : J ∈ RigidSet fullQ x) (hvN : v ∈ Subgroup.normalizer (J : Set G))
    (hvact : v ∉ centralizerSection J (pPrimeCoreOf 2 J))
    (hxP : x ∈ Kz fullQ x)
    (hmax : ∀ s : G, orderOf s = 2 →
      Nat.card ↥(RigidSet fullQ s) ≤ Nat.card ↥(RigidSet fullQ x))
    (h81 : ∀ y : G, IsConj x y → y * x = x * y → ∀ hyJ : y ∈ Subgroup.normalizer (J : Set G),
      y ∉ centralizerSection J (pPrimeCoreOf 2 J) →
      MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨y, hyJ⟩) ∉
        (MulAut.conj : kBar J →* MulAut (kBar J)).range) :
    False := by
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  let L : Subgroup G := CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap g J
  have hL : L ∈ RigidSet fullQ v := by
    rw [← hg, rigidSet_conj]
    exact Set.mem_image_of_mem _ hJ
  obtain ⟨V, hVx, hVv, hVZ, hV2, hVc, hV4⟩ :=
    exists_fixed_center_subgroup hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN hvact
      hxP hmax hL
  refine false_of_not_inner_of_four_le_card hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ
    hvN hvact hxP hmax hL hVx hVZ hV2 hVc hV4 ?_
  intro a haV haJ hainn
  by_contra hane
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨a, haV⟩
  have hm' : orderOf a = 2 ^ m :=
    (Subgroup.orderOf_coe (⟨a, haV⟩ : ↥V)).trans hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hane (orderOf_eq_one_iff.mp (by simpa using hm'))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hne0 : orderOf a ≠ 0 := by
    rw [hm']
    exact pow_ne_zero _ (by norm_num)
  have hdvd : 2 ∣ orderOf a := by
    rw [hm', pow_succ]
    exact ⟨2 ^ k, by ring⟩
  let a' : G := a ^ (orderOf a / 2)
  have ha'2 : orderOf a' = 2 := by
    simpa [a'] using orderOf_pow_orderOf_div (x := a) (n := 2) hne0 hdvd
  have ha'x : a' ∈ Subgroup.centralizer ({x} : Set G) := by
    simpa [a'] using
      Subgroup.pow_mem (Subgroup.centralizer ({x} : Set G)) (hVx haV) (orderOf a / 2)
  have ha'v : a' ∈ Subgroup.centralizer ({v} : Set G) := by
    simpa [a'] using
      Subgroup.pow_mem (Subgroup.centralizer ({v} : Set G)) (hVv haV) (orderOf a / 2)
  have ha'Z : a' ∈ zStar L := by
    simpa [a'] using Subgroup.pow_mem (zStar L) (hVZ haV) (orderOf a / 2)
  have ha'J : a' ∈ Subgroup.normalizer (J : Set G) := by
    simpa [a'] using
      Subgroup.pow_mem (Subgroup.normalizer (J : Set G)) haJ (orderOf a / 2)
  have hainn' : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a', ha'J⟩) ∈
      (MulAut.conj : kBar J →* MulAut (kBar J)).range := by
    have hsub : (⟨a', ha'J⟩ : Subgroup.normalizer (J : Set G)) =
        (⟨a, haJ⟩ : Subgroup.normalizer (J : Set G)) ^ (orderOf a / 2) :=
      Subtype.ext (by rfl)
    have h2 : J.normalizerMonoidHom ⟨a', ha'J⟩ =
        (J.normalizerMonoidHom ⟨a, haJ⟩) ^ (orderOf a / 2) := by
      rw [hsub, map_pow]
    have h3 : MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a', ha'J⟩) =
        (MulAut.mapQuotient (pPrimeCore 2 ↥J) (J.normalizerMonoidHom ⟨a, haJ⟩)) ^
          (orderOf a / 2) := by
      rw [h2, map_pow]
    rw [h3]
    exact Subgroup.pow_mem _ hainn _
  exact false_of_inner_involution_mem_zStar hnonab hKproper hL34 h16 hx2 hv2 hxv hvx hJ hvN
    hvact hxP hmax h81 hL ha'2 ha'x ha'v ha'Z ha'J hainn'

end CFSG.GH74.GLS.NT44

end
