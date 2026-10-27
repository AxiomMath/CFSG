module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Two
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4Two

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem i1021_pRank_top_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    (K : Subgroup G) : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ CFSG.Open.pRank p K := by
  have := CFSG.SectionRank.pRank_le_map hp K.subtype K.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at this

theorem input10_21_holds :
    LocalBalance.CaseThreeNs.Input10_21 := by
  refine ⟨?_, ?_⟩
  · intro G _ _ K _ hF
    obtain ⟨e⟩ := hF
    obtain ⟨V, hV, hVc⟩ := i1021_fi22_two_rank_five e
    exact (i1021_fi22_of_two_rank e hV hVc ↥K (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)).trans (i1021_pRank_top_le (by norm_num) K)
  · intro G _ _ K _ hF
    obtain ⟨V, hV, hVc⟩ := i1021_d4_two_rank_four hF
    exact (i1021_d4_of_two_rank hF hV hVc ↥K (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)).trans (i1021_pRank_top_le (by norm_num) K)

end CFSG.HardMathSupport.Solomon.Coordinator
