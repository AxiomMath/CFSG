module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Core
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Facts
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Steps

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem Point.ne_top (hx : Point P M x) : M ≠ ⊤ := fun h => hx.not_le (h ▸ le_top)

theorem plane63_of_situation (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    Plane63 p ↥M (P.subtype hS.sylow_le) ⟨x, hx.mem_M hS⟩ ⟨z, hS.sylow_le hz.mem⟩ := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hxM : x ∈ M := hx.mem_M hS
  have hzM : z ∈ M := hS.sylow_le hz.mem
  refine ⟨hprime, hS.p_ge,
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper M
      hx.ne_top, ?_, ?_, ?_, ?_, ?_, fun N _ hN => eq_top_of_isPGroup_quotient hS N hN⟩
  · exact smallRankPlane_subgroupOf hS.sylow_le hxM hzM (plane_of_central hS hx hz)
  · rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (mem_centralizer_iff.mp hz.centralizes (h : G) hh)
  · have h4 := hS.four_le_pRank
    change 4 ≤ Open.pRank p ((P : Subgroup G).subgroupOf M)
    rwa [pRank_subgroupOf hprime.one_lt hS.sylow_le]
  · calc Open.pRank p (centralizer ({(⟨x, hxM⟩ : M)} : Set M))
        = Open.pRank p ((centralizer ({(⟨x, hxM⟩ : M)} : Set M)).map M.subtype) :=
          (pRank_map_subtype hprime.one_lt _).symm
      _ ≤ Open.pRank p (centralizer ({x} : Set G)) := by
          refine CFSG.SectionRank.pRank_mono hprime.one_lt ?_
          rintro _ ⟨y, hy, rfl⟩
          exact mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      _ ≤ 2 := hx.pRank_centralizer_le hS
  · set x' : M := ⟨x, hxM⟩ with hx'
    have hPM := hS.sylow_le
    have hB : (centralizer ({x'} : Set M)).map M.subtype = M ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'))⟩
      · rintro ⟨hyM, hyC⟩
        exact ⟨⟨y, hyM⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC)), rfl⟩
    have hA : ((P.subtype hPM : Subgroup M) ⊓ centralizer ({x'} : Set M)).map M.subtype =
        (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      ext y
      constructor
      · rintro ⟨y', ⟨hy'P, hy'C⟩, rfl⟩
        exact ⟨hy'P, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy'C))⟩
      · rintro ⟨hyP, hyC⟩
        exact ⟨⟨y, hPM hyP⟩, ⟨hyP, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M, hA, hB]
    exact CFSG.ABGLocalTools.IsSylowOf.of_le hx.sylow (inf_le_inf_right _ hPM) inf_le_right

theorem stepL63_of_kfacts (hA : KFactSingleComponent) (hB : KFactMultiComponent) : StepL63 := by
  intro G _ _ p P M x z hS hx hz hcon
  have hprime := hS.prime
  have hxM : x ∈ M := hx.mem_M hS
  have hzM : z ∈ M := hS.sylow_le hz.mem
  have hpl := plane63_of_situation hS hx hz
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    sup_le (zpowers_le.mpr hxM) (zpowers_le.mpr hzM)
  intro T hT
  have hT' := isMaxTwoInvariantIn_top hBM hT
  rw [← plane_eq_subgroupOf (⟨x, hxM⟩ : M) ⟨z, hzM⟩] at hT'
  suffices hkey : Open.pRank p ((P.subtype hS.sylow_le : Sylow p M) : Subgroup M) ≤
      Open.pRank p (normalizer ((T.subgroupOf M : Subgroup M) : Set M)) by
    rw [pRank_normalizer_subgroupOf hprime.one_lt hT.1.1] at hkey
    change Open.pRank p ((P : Subgroup G).subgroupOf M) ≤ _ at hkey
    rwa [pRank_subgroupOf hprime.one_lt hS.sylow_le] at hkey
  obtain ⟨L₀, hL₀, -⟩ := CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component
    hS.toGlobal.d1Global.kProper M hx.ne_top p hprime hcon
  by_cases huniq : ∃ L : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf K ⊤ → K = L
  · rcases hA p M _ _ _ hpl huniq with h1 | h2
    · exact h1 _ hT'
    · have hcop : Nat.Coprime p (Nat.card (T.subgroupOf M)) := by
        obtain ⟨k, hk⟩ := (hT'.1.2.1 : IsPGroup 2 (T.subgroupOf M)).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime Nat.prime_two).mpr hS.ne_two)
      have hBinv : zpowers (⟨x, hxM⟩ : M) ⊔ zpowers (⟨z, hzM⟩ : M) ≤
          normalizer ((T.subgroupOf M : Subgroup M) : Set M) := hT'.1.2.2
      exact normalizerRank_of_le_core hprime hS.ne_two
        (hpl.plane.isIsolatedPlane.1) hT' (h2 _ hcop hBinv)
  · obtain ⟨K, hK, hKL⟩ : ∃ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
        IsComponentOf K ⊤ ∧ K ≠ L₀ := by
      by_contra hno
      push Not at hno
      exact huniq ⟨L₀, hL₀, hno⟩
    exact hB p M _ _ _ hpl ⟨K, L₀, hK, hL₀, hKL⟩ _ hT'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
