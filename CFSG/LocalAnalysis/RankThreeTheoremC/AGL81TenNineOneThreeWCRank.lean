module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCore
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open TenNineOneThree (IsWClosed)
open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

theorem four_le_pRank_ree
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {m : ℕ}
    (hd : d.1 = .reeG2 m) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
  omega

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_three_of_cfg (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K) :
    Open.pRank 3 K ≤ 3 := by
  have h1 : Open.pRank 3 K ≤ Open.pRank 3 (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :=
    CFSG.SectionRank.pRank_mono (by norm_num) le_top
  have h2 := primeComplementCore_quotient_pRank_eq (G := H) 3 Nat.prime_three
  have h3 : Open.pRank 3 (⊤ : Subgroup H) = Open.pRank 3 H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  have h4 := local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hd.maxH.1
  rw [hS.rank] at h4
  calc Open.pRank 3 K ≤ _ := h1
    _ = Open.pRank 3 (⊤ : Subgroup H) := h2
    _ = Open.pRank 3 H := h3
    _ ≤ 3 := h4

end CFSG.LocalAnalysis.RankThreeTheoremC
