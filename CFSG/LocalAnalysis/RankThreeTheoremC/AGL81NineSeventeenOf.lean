module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenProjection
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenFirst
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeRankTwoOf
import CFSG.LocalAnalysis.GLTheoremA.S8.Close

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_cover_witness {p : ℕ} {M H N : Subgroup G}
    (hcov : AGLCovers p H N (d1KBar p M H)) :
    ∃ W : Subgroup G, ∃ _ : W ≤ H ⊓ N,
      (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = d1KBar p M H := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  refine ⟨(H ⊓ N) ⊓ ((d1KBar p M H).comap π).map H.subtype, inf_le_left, ?_⟩
  refine le_antisymm ?_ fun k hk => ?_
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨-, h', hh', he'⟩ := Subgroup.mem_subgroupOf.mp hh
    have : h' = h := Subtype.ext he'
    rw [← this]
    exact hh'
  · obtain ⟨h, hh, rfl⟩ := hcov hk
    exact ⟨h, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hh, h, hk, rfl⟩, rfl⟩

theorem agl81NineSeventeenQ_of (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR2 : KFactNineThreeRankTwo)
    (hSch : KFactCatalogSchreier) (hS : Setting G) (hNC : AGL81NineSeventeenNotConstrained G) :
    AGL81NineSeventeenQ G := by
  intro hg p P M H hμ hH hHM hKex B N hB hBH hN hNM hBN hcov
  obtain ⟨H₁, R₁, he⟩ := hμ.escape
  have hKN := hNC hg p P M H hμ hH hHM hKex B N hB hBH hN hNM hBN hcov
  have hKH : d1KBar p M H ≠ ⊥ := by
    obtain ⟨L, hL, hLX⟩ := hKex
    intro h
    exact not_le_bot_of_isComponentOf hL (h ▸ le_d1KBar hL hLX)
  have hHtop : H ≠ ⊤ := CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hH.1
  have hNtop : N ≠ ⊤ := CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hN.1
  obtain ⟨hinv, hκ, hfac⟩ := nineSeventeen_involves h31 h75 hOut hR2 hSch hS hg.kProper he hB hBH
    hBN hHtop hNtop hKH hKN hcov
  obtain ⟨W, hW, hWK⟩ := exists_cover_witness hcov
  refine ⟨hKN, ⟨W, hW, hWK, ?_⟩, hκ, Or.inr (Or.inr hinv)⟩
  rcases hκ.eq_or_lt with h | h
  · exact Or.inr (Or.inl (hfac h))
  · exact Or.inr (Or.inr h)

theorem agl81NineCompetitorQ_of_nineSeventeen (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR1 : KFactNineThreeListRankOne)
    (hSyl : KFactCaseTwoSylowAut) (hSch : KFactCatalogSchreier) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hNC2 : AGL81NineSeventeenNotConstrainedTwo G) (hS : Setting G) :
    AGL81NineCompetitorQ G :=
  have hR2 := kFactNineThreeRankTwo_of_listRankOne hR1
  agl81NineCompetitorQ_of_kfacts h31 h75 hOut hR2
    (agl81NineSeventeenQ_of h31 h75 hOut hR2 hSch hS
      (agl81NineSeventeenNotConstrained_of h31 h75 hR1 hSyl h74 hOutC hS hNC2)) hS

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
