module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Unit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCY
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem unique_of_uniquePComponent {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥)
    (h : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧
      ∀ K : Subgroup Y, IsComponentOf K ⊤ → p ∣ Nat.card K → K = L) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L := by
  obtain ⟨L, hL, -, hu⟩ := h
  exact ⟨L, hL, fun K hK => hu K hK
    (CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.dvd_card_comp hcore
      ⟨K, (CFSG.isComponent_iff_open K).2 hK⟩)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup I291

theorem kFactSingleComponentThreeRank_of_kdata (hMult : KDMultP5) (hEx : KDR3Exclusion) :
    KFactSingleComponentThreeRank := by
  intro A _ _ p P X x z hpl _ hU
  haveI : Fact p.Prime := ⟨hpl.prime⟩
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  have hYD := yData_of_plane63 (plane63_of_plane65 hpl hxX hzX)
  obtain ⟨L, hL, hLu⟩ := unique_of_uniquePComponent hYD.cfg.core hU
  have key := two_le_pRank_three_of_single hMult hEx
    (linUniE9_of_uniE9 uniE9_holds hpl.five_le) hYD.cfg hYD.four_le hYD.rank_cent hYD.perf hL hLu
  have hX3 := two_le_pRank_three_of_surjective
    (QuotientGroup.mk' (primeComplementCore (G := ↥X) p))
    (QuotientGroup.mk'_surjective _) key
  rw [pRank_subgroup_eq_internal_top 3 (by norm_num) X]
  exact hX3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
