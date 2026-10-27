module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiPart
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65M

theorem plane63_of_plane65 {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A}
    {X : Subgroup A} {x z : A} (h : Plane65 p P X x z) (hx : x ∈ X) (hz : z ∈ X) :
    Plane63 p ↥X (P.subtype h.sylow_le) ⟨x, hx⟩ ⟨z, hz⟩ := by
  have hprime := h.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  refine ⟨hprime, h.five_le, h.catalog, ?_, ?_, ?_, ?_, ?_, h.perfect⟩
  · exact smallRankPlane_subgroupOf h.sylow_le hx hz h.plane
  · rw [mem_centralizer_iff]
    intro g hg
    exact Subtype.ext (mem_centralizer_iff.mp h.z_central (g : A) hg)
  · have h4 := h.four_le
    change 4 ≤ Open.pRank p ((P : Subgroup A).subgroupOf X)
    rwa [pRank_subgroupOf hprime.one_lt h.sylow_le]
  · calc Open.pRank p (centralizer ({(⟨x, hx⟩ : X)} : Set X))
        = Open.pRank p ((centralizer ({(⟨x, hx⟩ : X)} : Set X)).map X.subtype) :=
          (pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank p (centralizer ({x} : Set A)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := h.rank_centralizer
  · set x' : X := ⟨x, hx⟩ with hx'
    have hPM := h.sylow_le
    have hB : (centralizer ({x'} : Set X)).map X.subtype = X ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPM : Subgroup X) ⊓ centralizer ({x'} : Set X)).map X.subtype =
        (P : Subgroup A) ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPM hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le h.sylow_centralizer (inf_le_inf_right _ hPM)
      inf_le_right

theorem kFactP65Multi_of_partI (h64 : KFactCenterCyclicGeFive) (h610 : GL83.I_6_10_1)
    (h7131 : GL83.I_7_13_1) (hsplit : KFactSylowSplit) : KFactP65Multi := by
  intro A _ _ p P X x z hpl hcomp
  have hprime := hpl.prime
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  have hBX : zpowers x ⊔ zpowers z ≤ X := hBP.trans hPX
  have hpl63 := plane63_of_plane65 hpl hxX hzX
  obtain ⟨L, K, hL, -, hK, -, hLK⟩ := hcomp
  have hcomp' : ∃ L K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K := ⟨L, K, hL, hK, hLK⟩
  refine ⟨fun f F hf hfp hF => ?_, fun E hEX hE hEc => ?_⟩
  ·
    have hβ : KFactBetaStructure := kFactBetaStructure_of_partI h64 h610 h7131 hsplit
    have hT' := isMaxFInvariantIn_top hBX hF
    rw [← plane_eq_subgroupOf (⟨x, hxX⟩ : X) ⟨z, hzX⟩] at hT'
    have hkey := pRank_le_normalizer_of_beta hβ hf hfp hpl63 hcomp' hT'
    rw [pRank_normalizer_subgroupOf hprime.one_lt hF.1.1] at hkey
    change Open.pRank p ((P : Subgroup A).subgroupOf X) ≤ _ at hkey
    rwa [pRank_subgroupOf hprime.one_lt hPX] at hkey
  ·
    have hE' : IsElemAbelian p (E.subgroupOf X) := IsElemAbelian.subgroupOf hE X
    have hEc' : Nat.card (E.subgroupOf X) = p ^ p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hEc]
    obtain ⟨a, ha, ha1, b, hb, hb1, hg⟩ :=
      exists_pair_of_plane63 h64 h610 h7131 hsplit hpl63 hcomp' hE' hEc'
    refine ⟨(a : A), ha, fun h => ha1 (Subtype.ext h), (b : A), hb, fun h => hb1 (Subtype.ext h),
      fun g hgm hgz => ?_⟩
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hgz
    refine hg ⟨g, hgm.1⟩ (mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩)
    simpa using hm

theorem kFactP65Multi_holds
    : KFactP65Multi :=
  kFactP65Multi_of_partI CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds
    GL83.I_6_10_1_proved GL83.I713.i_7_13_1_holds K713S.kFactSylowSplit_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
