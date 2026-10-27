module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L63
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

@[expose] def NoTwoComponentsPlane : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X), N3.Plane63E3 p X P x z →
    ¬ ∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧ IsComponentOf K ⊤ ∧ K ≠ L

theorem n4_plane63E3_of_plane65E3 {A : Type} [Group A] [Finite A] {p : ℕ} {P : Sylow p A}
    {X : Subgroup A} {x z : A} (hpl : Plane65E3 p P X x z) :
    ∃ (hxX : x ∈ X) (hzX : z ∈ X),
      N3.Plane63E3 p ↥X (P.subtype hpl.sylow_le) ⟨x, hxX⟩ ⟨z, hzX⟩ := by
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPX := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  refine ⟨hxX, hzX, hprime, hpl.five_le, hpl.catalog, ?_, ?_, ?_, ?_, ?_⟩
  · exact smallRankPlane_subgroupOf hPX hxX hzX hpl.plane
  · rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (mem_centralizer_iff.mp hpl.z_central (h : A) hh)
  · change Open.pRank p ((P : Subgroup A).subgroupOf X) = 3
    rw [pRank_subgroupOf hprime.one_lt hPX]
    exact hpl.pRank_eq
  · calc Open.pRank p (centralizer ({(⟨x, hxX⟩ : X)} : Set X))
        = Open.pRank p ((centralizer ({(⟨x, hxX⟩ : X)} : Set X)).map X.subtype) :=
          (pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank p (centralizer ({x} : Set A)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := hpl.rank_centralizer
  · have hB : (centralizer ({(⟨x, hxX⟩ : X)} : Set X)).map X.subtype =
        X ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPX : Subgroup X) ⊓ centralizer ({(⟨x, hxX⟩ : X)} : Set X)).map
        X.subtype = (P : Subgroup A) ⊓ centralizer ({x} : Set A) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPX hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hpl.sylow_centralizer
      (inf_le_inf_right _ hPX) inf_le_right

theorem kFactP65SingleAt_of_single (hW : KFactSingleW) (hβ : NoTwoComponentsPlane) (p : ℕ) :
    KFactP65SingleAt p := by
  intro A _ _ P X x z hpl _ _ hU W hWX hWcop hBW
  obtain ⟨hxX, hzX, hpl'⟩ := n4_plane63E3_of_plane65E3 hpl
  have hprime := hpl.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPX := hpl.sylow_le
  have huniq : ∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf K ⊤ → K = L := by
    obtain ⟨L, hL, hLp, hLu⟩ := hU
    refine ⟨L, hL, fun K hK => ?_⟩
    by_contra hKL
    exact hβ p ↥X _ _ _ hpl' ⟨L, K, hL, hLp, hK, hKL⟩
  have hBW' : zpowers (⟨x, hxX⟩ : X) ⊔ zpowers (⟨z, hzX⟩ : X) ≤
      normalizer ((W.subgroupOf X : Subgroup X) : Set X) := by
    rw [plane_eq_subgroupOf (⟨x, hxX⟩ : X) ⟨z, hzX⟩, ← Subgroup.subgroupOf_normalizer_eq hWX]
    intro b hb
    exact hBW hb
  have hWcop' : Nat.Coprime p (Nat.card (W.subgroupOf X)) := by
    have h1 : Nat.card (W.subgroupOf X) = Nat.card W :=
      Nat.card_congr (subgroupOfEquivOfLe hWX).toEquiv
    rw [h1]
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left p 2) hWcop).symm
  have hsub := hW p ↥X _ _ _ hpl' hpl.perfect huniq (W.subgroupOf X) hWcop' hBW'
  intro w hw
  have hwX : w ∈ X := hWX hw
  have h1 : (⟨w, hwX⟩ : X) ∈ primeComplementCore (G := ↥X) p := hsub hw
  have heq : rankThreePrimeCore p X = (primeComplementCore (G := ↥X) p).map X.subtype :=
    CFSG.AGLEmbedding.glbPrimeCore_eq_primeComplementCoreOf p X
  rw [heq]
  exact ⟨⟨w, hwX⟩, h1, rfl⟩

theorem kFactP65SingleE3_of_single (hW : KFactSingleW) (hβ : NoTwoComponentsPlane) :
    KFactP65SingleE3 :=
  fun A _ _ p P X x z hpl _ hX hrank hU W hWX hWcop hBW =>
    kFactP65SingleAt_of_single hW hβ p A P X x z hpl hX hrank hU W hWX hWcop hBW

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
