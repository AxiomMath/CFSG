module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallCover

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoClassical

theorem exists_sq_eq_one_notMem_center {G : Type} [Group G] [Finite G] {A R T : Subgroup G}
    {g : G} (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    ∃ p : A, p ^ 2 = 1 ∧ p ∉ center A := by
  obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.T_ne_bot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨p, hp, r, hr, rfl⟩ := exists_mul_of_mem_T hc h32 h4 h34 htT
  have hrC : r ∈ centralizer (A : Set G) := hc.sylowR.le hr
  refine ⟨⟨p, hp⟩, Subtype.ext ?_, fun hpZ => ht1' ?_⟩
  ·
    have hpr : Commute p r := mem_centralizer_iff.mp hrC p hp
    have ht2 : (p * r) ^ 2 = 1 := (hc.elemT h32).2 _ htT
    rw [hpr.mul_pow, (hc.elemR h32).2 r hr, mul_one] at ht2
    exact ht2
  ·
    have hpC : p ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (mem_center_iff.mp hpZ ⟨b, hb⟩)
    have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
      rw [AS76b.normalizer_centralizer_eq hc.hyp.standard]
      exact hc.not_mem
    have hTK : T ⊓ centralizer (A : Set G) = ⊥ :=
      two_subgroup_inf_conjugate_eq_bot _ T (AS76b.tightlyEmbedded_centralizer hc.hyp.standard)
        hc.sylowT.isPGroup g hgK hc.sylowT.le
    have hmem : p * r ∈ T ⊓ centralizer (A : Set G) := ⟨htT, mul_mem hpC hrC⟩
    rwa [hTK, mem_bot] at hmem

theorem altEvenCenterSmall_of (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hcfg : Section3Config) : AltEvenCenterSmall := by
  intro G _ _ A hH hO n hn5 hn7 ⟨e⟩
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO hn5 e)
  obtain ⟨p, hp2, hpZ⟩ := exists_sq_eq_one_notMem_center hc h32 h4 h34
  have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hH.standard.1.1
  by_contra hodd
  apply hpZ
  rw [← ker_quotCenterHom e]
  exact alternatingCover_mem_ker_of_sq_eq_one hn5 hn7 (quotCenterHom e)
    (quotCenterHom_surjective e) (ker_quotCenterHom e).le
    (by rw [ker_quotCenterHom]; exact Nat.not_odd_iff_even.mp hodd) hp2

theorem altEvenCenterSmall :
    AltEvenCenterSmall :=
  altEvenCenterSmall_of RankTwoFoundation.lemma32 RankTwoFoundation.asc75Theorem4
    AS76b.asc08Lemma34 RankTwoFoundation.section3Config

end CFSG.ComponentClassification.RankTwoAlt
