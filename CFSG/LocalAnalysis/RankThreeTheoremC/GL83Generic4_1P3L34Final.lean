module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Finalb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Inspectc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_stepK (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK3 : KFactL34Unitary)
    (hK4 : KFactL34Borel) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) {U : Subgroup G} (hU : IsElemAbelian 3 U) (_hUc : Nat.card U = 3 ^ 2)
    (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥) {S₁ H : Subgroup G}
    (hUS₁ : U ≤ normalizer (S₁ : Set G))
    (hsyl : IsSylowOf 2 (l34Img x J (S₁ ⊓ J)) (l34Img x J J))
    (hS₁H : S₁ ≤ H) (hUH : U ≤ H) (hrk : pRank 3 H ≤ 2) {r : G} (hrH : r ∈ H)
    (hrO : r ∈ GLBPrimeCore 3 M) (hrC : r ∈ centralizer ({x} : Set G))
    (hr2 : ∃ k : ℕ, r ^ 2 ^ k = 1) (hr1 : r ≠ 1) : False := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hUC : U ≤ C := fun g hg => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxU⟩))
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hUJ
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu3 : u ^ 3 = 1 := hU.2 u hu.1
  have huC : u ∈ C := hUC hu.1
  obtain ⟨hKn, hKc, hKt⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hTe, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  set K : Subgroup (L34Quot x J) := l34Img x J J with hK
  set S₂ : Subgroup (L34Quot x J) := l34Img x J (S₁ ⊓ J) with hS₂
  set Jt : Subgroup (L34Quot x J) := l34Img x J H with hJt
  set ut : L34Quot x J := l34Hom x J ⟨u, huC⟩ with hut
  have hutK : ut ∈ K := ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr hu.2, rfl⟩
  have hutT : ut ∈ l34Img x J ((P : Subgroup G) ⊓ J) :=
    ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr ⟨hUP hu.1, hu.2⟩, rfl⟩
  have hutJt : ut ∈ Jt := ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.mpr (hUH hu.1), rfl⟩
  have huto : orderOf ut = 3 := by
    refine orderOf_eq_prime ?_ fun h => hu1' (l34insp_eq_one_of_three hK1 hK2 hJ hu.2 hu3 h)
    rw [hut, ← map_pow]
    have : (⟨u, huC⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [this, map_one]
  have hutN : ut ∈ normalizer (S₂ : Set (L34Quot x J)) :=
    l34insp_hom_mem_normalizer x J (S₁ ⊓ J)
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hUS₁ hu.1, hJ.centralizer_le huC⟩)
  have hS₂Jt : S₂ ≤ Jt :=
    Subgroup.map_mono fun c hc => Subgroup.mem_subgroupOf.mpr
      (hS₁H (Subgroup.mem_subgroupOf.mp hc).1)
  have hS₂K : S₂ ≤ K := hsyl.le
  have hBorel : normalizer (S₂ : Set (L34Quot x J)) ⊓ K ≤ Jt ⊓ K := by
    obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
    have huKN : (⟨ut, hutK⟩ : ↥K) ∈ normalizer ((S₂.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hS₂K]
      exact hutN
    have hmax : rankTwoMaximalInvariantTwoSubgroup (zpowers (⟨ut, hutK⟩ : ↥K))
        (S₂.subgroupOf K) := by
      refine ⟨by rw [← hQ]; exact Q.isPGroup', zpowers_le.mpr huKN, fun L hL2 _ hVL => ?_⟩
      rw [← hQ] at hVL ⊢
      exact Q.3 hL2 hVL
    obtain ⟨-, -, hN⟩ := hK4 ↥K hKt ⟨ut, hutK⟩ (by rw [Subgroup.orderOf_mk]; exact huto) _ hmax
    intro n hn
    have hn' : (⟨n, hn.2⟩ : ↥K) ∈ zpowers (⟨ut, hutK⟩ : ↥K) ⊔ S₂.subgroupOf K := by
      rw [hN, ← Subgroup.subgroupOf_normalizer_eq hS₂K]
      exact hn.1
    have hle : zpowers (⟨ut, hutK⟩ : ↥K) ⊔ S₂.subgroupOf K ≤ (Jt ⊓ K).subgroupOf K :=
      sup_le (zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr ⟨hutJt, hutK⟩)) fun s hs =>
        Subgroup.mem_subgroupOf.mpr ⟨hS₂Jt (Subgroup.mem_subgroupOf.mp hs), s.2⟩
    exact Subgroup.mem_subgroupOf.mp (hle hn')
  have hβ1 : l34Hom x J ⟨r, hrC⟩ ≠ 1 := by
    obtain ⟨k, hk⟩ := hr2
    exact fun h => hr1 (congrArg Subtype.val
      (l34insp_eq_one_of_two hS hU0 hD1 hK1 hK2 hp hM hgen hJ (c := ⟨r, hrC⟩) hk h))
  have hβJt : l34Hom x J ⟨r, hrC⟩ ∈ Jt := ⟨⟨r, hrC⟩, Subgroup.mem_subgroupOf.mpr hrH, rfl⟩
  have hβN : l34Hom x J ⟨r, hrC⟩ ∈
      normalizer ((Jt ⊓ K : Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hβJt, ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact Subgroup.mem_top _
  have hDK : Jt ⊓ K = K := ((hK3 (L34Quot x J) K hKn hKc hKt _ hTe hTc hTK).2 _
    (l34_lemma44_image hS hU0 hK1 hK2 hp hM hgen hJ ⟨r, hrC⟩ hrO)).2 hβ1 S₂ hS₂K hsyl ut hutT
    huto hutN (Jt ⊓ K) inf_le_right hBorel hβN
  have hbar := l34fin_bar_le hS hU0 hK1 hK2 hp hM hgen hJ (hDK.ge.trans inf_le_left)
  obtain ⟨E⟩ : Nonempty (Sylow 3 ↥(r1sBar x J)) := inferInstance
  obtain ⟨hEe, hEc, -⟩ := r1sBar_sylow_facts_l34 hK1 hK2 hJ E
  set Eb : Subgroup (GenericReduced 3 x) :=
    (E : Subgroup ↥(r1sBar x J)).map (r1sBar x J).subtype with hEb
  have hEbe : IsElemAbelian 3 Eb :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEe _
  have hEbc : Nat.card Eb = 3 ^ 2 := by
    rw [hEb, Subgroup.card_map_of_injective (r1sBar x J).subtype_injective]
    exact hEc
  have hEbJ : Eb ≤ r1sBar x J := Subgroup.map_subtype_le _
  set xb : GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) ⟨x, hxC⟩
    with hxb
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxC⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hxJ : x ∉ J := fun h =>
    hx1 (l34insp_eq_one_of_three hK1 hK2 hJ h hx3 (l34insp_hom_self hJ))
  have hxbE : xb ∉ Eb := fun h => hxJ (r1s_mem_of_mk_mem_l34 hJ hxC hx3 (hEbJ h))
  have hxbc : ∀ e ∈ Eb, e * xb = xb * e := by
    intro e _
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := C) 3) e
    rw [hxb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
  have hcard : Nat.card (Eb ⊔ zpowers xb : Subgroup (GenericReduced 3 x)) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime Eb hxb3 hxbE hxbc, hEbc]
    norm_num
  have hEA : IsElemAbelian 3 (Eb ⊔ zpowers xb) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hEbe
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hxb3)
      (le_centralizer_iff.mpr (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hxbc e he)))
  have h3 := l34fin_le_pRank_of_le_map (primeComplementCore_coprime 3) hEA hcard
    (sup_le (hEbJ.trans hbar)
      (zpowers_le.mpr ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr (hUH hxU), rfl⟩))
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
