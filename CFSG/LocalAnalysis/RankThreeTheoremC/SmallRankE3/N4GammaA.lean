module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4KGRestrict
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L63
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4GammaCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.GH74.Uniqueness.SU

variable {G : Type} [Group G] [Finite G]

theorem n4_pSolvable_centralizer_of_gammaCent (hγc : N3.GammaCentP) (hβ : NoTwoComponentsGen)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G) (hsit : SmallRankSituation G p P M)
    (hp5 : 5 ≤ p) (hcon : ¬ HasPrimeConstraint (G := M) p) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {b : G} (hbB : b ∈ zpowers x ⊔ zpowers z) (hbZ : b ∉ zpowers z) :
    CFSG.HallHigman.IsPSolvable p ↥(M ⊓ centralizer ({b} : Set G)) := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hxM, hzM, hpl⟩ := n4_plane63E3 hS hsit hp5 hx hz
  have hne : M ≠ ⊤ := fun h => hx.not_centralizer_le (h ▸ le_top)
  have hpl' := SmallRankPlane.of_situation hS hsit hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl'.isIsolatedPlane.1
  have hbP : b ∈ (P : Subgroup G) := hBP hbB
  have hbM : b ∈ M := hPM hbP
  obtain ⟨hBc, hBp⟩ := SU1.isElemAbelian_iff.mp hpl'.isElemAbelian
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ one_mem _)
  have hbp : b ^ p = 1 := hBp b hbB
  have hcent2 := n4_pRank_centralizer_le_of_mem_plane hS hsit hx hz hbB hbZ
  have hCeq : centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M) =
      (M ⊓ centralizer ({b} : Set G)).subgroupOf M := by
    ext m
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subtype.ext_iff, Subgroup.coe_mul]
    exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
  have hCrank : Open.pRank p (centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M)) = 2 := by
    rw [hCeq, pRank_subgroupOf hprime.one_lt (inf_le_left : M ⊓ centralizer ({b} : Set G) ≤ M)]
    refine le_antisymm
      ((CFSG.SectionRank.pRank_mono hprime.one_lt inf_le_right).trans hcent2) ?_
    have hBM : zpowers x ⊔ zpowers z ≤ M ⊓ centralizer ({b} : Set G) := fun w hw =>
      ⟨hPM (hBP hw), Subgroup.mem_centralizer_singleton_iff.mpr (hBc b hbB w hw).symm⟩
    exact CFSG.SectionRank.le_pRank hprime.one_lt hBM hpl'.isElemAbelian hpl'.card_eq
  obtain ⟨L₀, hL₀, -, -, hpL₀, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper M hne p
      hprime hcon
  have huniq : ∃ L : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p), IsComponentOf K ⊤ → K = L := by
    by_contra hno
    obtain ⟨K, hK', hKL⟩ : ∃ K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
        IsComponentOf K ⊤ ∧ K ≠ L₀ := by
      by_contra hno'
      push Not at hno'
      exact hno ⟨L₀, hL₀, hno'⟩
    exact hβ G hS p hp5 P M hsit x z hx hz ⟨L₀, K, hL₀, hpL₀, hK', hKL⟩
  have h3 : ∀ Q : Subgroup ↥M, Q ≠ ⊥ → IsPGroup 2 Q →
      Open.pRank 3 (normalizer (Q : Set ↥M)) ≤ 3 := by
    intro Q hQ hQ2
    have h3G : ∀ Q₀ : Subgroup G, Q₀ ≠ ⊥ → IsPGroup 2 Q₀ →
        Open.pRank 3 (normalizer (Q₀ : Set G)) ≤ 3 := by
      intro Q₀ hQ₀ hQ₀2
      have hloc : IsTwoLocal (normalizer (Q₀ : Set G)) := ⟨Q₀, hQ₀, hQ₀2, rfl⟩
      have h1 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) _ hloc
      have h2 := hS.rank
      omega
    set Q₀ : Subgroup G := Q.map M.subtype with hQ₀def
    have hQ₀M : Q₀ ≤ M := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hQ₀ne : Q₀ ≠ ⊥ := by
      intro h
      apply hQ
      rw [eq_bot_iff]
      intro y hy
      have : (y : G) ∈ Q₀ := ⟨y, hy, rfl⟩
      rw [h] at this
      exact Subtype.ext (Subgroup.mem_bot.mp this)
    have hQ₀2 : IsPGroup 2 Q₀ :=
      hQ2.of_equiv (Q.equivMapOfInjective M.subtype M.subtype_injective)
    have hQeq : Q = Q₀.subgroupOf M :=
      (Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q).symm
    have hN : normalizer (Q : Set ↥M) = (normalizer (Q₀ : Set G)).subgroupOf M := by
      rw [hQeq]
      exact n4_normalizer_subgroupOf hQ₀M
    have hN' : (normalizer (Q₀ : Set G)).subgroupOf M =
        (M ⊓ normalizer (Q₀ : Set G)).subgroupOf M := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hN, hN', pRank_subgroupOf (by norm_num : 1 < 3) (inf_le_left :
      M ⊓ normalizer (Q₀ : Set G) ≤ M)]
    exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) inf_le_right).trans
      (h3G Q₀ hQ₀ne hQ₀2)
  have hres := hγc p hprime hp5 ↥M (P.subtype hPM) ⟨b, hbM⟩ hpl.catalog hbP
    (fun h => hb1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using hbp)) hpl.pRank_eq
    hCrank (fun N _ hN => n4_eq_top_of_isPGroup_quotient hS hsit N hN) h3 huniq
  rw [hCeq] at hres
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ centralizer ({b} : Set G) ≤ M)) hres

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
