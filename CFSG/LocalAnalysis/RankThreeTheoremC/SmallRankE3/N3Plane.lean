module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane)
open CFSG.AGLEmbedding (CatalogSimpleSections)

structure Plane63E3 (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  catalog : CatalogSimpleSections X
  plane : SmallRankPlane p (P : Subgroup X) x z
  z_central : z ∈ centralizer ((P : Subgroup X) : Set X)
  pRank_eq : Open.pRank p (P : Subgroup X) = 3
  rank_centralizer : Open.pRank p (centralizer ({x} : Set X)) ≤ 2
  sylow_centralizer : CFSG.ABGLocalTools.IsSylowOf p
    ((P : Subgroup X) ⊓ centralizer ({x} : Set X)) (centralizer ({x} : Set X))

theorem plane63E3_of_situation {G : Type} [Group G] [Finite G]
    (hS : CFSG.LocalAnalysis.RankThreeTheoremC.Setting G) {P : Sylow 5 G} {M : Subgroup G}
    (hs : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSituation G 5 P M) {x z : G}
    (hx : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPoint P M x)
    (hz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCentral P z) :
    ∃ (hPM : (P : Subgroup G) ≤ M) (hxM : x ∈ M) (hzM : z ∈ M),
      Plane63E3 5 ↥M (P.subtype hPM) ⟨x, hxM⟩ ⟨z, hzM⟩ := by
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hxM : x ∈ M := hPM hx.mem
  have hzM : z ∈ M := hPM hz.mem
  refine ⟨hPM, hxM, hzM, ?_⟩
  have hprime : Nat.Prime 5 := Nat.prime_five
  haveI : Fact (Nat.Prime 5) := ⟨hprime⟩
  have hne : M ≠ ⊤ := by
    intro h
    apply hx.not_centralizer_le
    rw [h]
    exact le_top
  refine ⟨hprime, le_refl _,
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hne, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.smallRankPlane_subgroupOf hPM hxM hzM
      (CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPlane.of_situation hS hs hx hz)
  · rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (mem_centralizer_iff.mp hz.centralizes (h : G) hh)
  · change Open.pRank 5 ((P : Subgroup G).subgroupOf M) = 3
    rwa [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_subgroupOf hprime.one_lt hPM]
  · calc Open.pRank 5 (centralizer ({(⟨x, hxM⟩ : M)} : Set M))
        = Open.pRank 5 ((centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype) :=
          (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank 5 (centralizer ({x} : Set G)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := by
          by_contra h
          push Not at h
          exact hs.largeObstruction_empty x
            ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩
  · have hB : (centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype =
        M ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPM : Subgroup M) ⊓ centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map
        M.subtype = (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPM hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    have hG : CFSG.ABGLocalTools.IsSylowOf 5 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
        (centralizer ({x} : Set G)) :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr
        ⟨inf_le_right, (P.isPGroup').to_le inf_le_left, hx.sylow_centralizer⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hG (inf_le_inf_right _ hPM) inf_le_right

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
