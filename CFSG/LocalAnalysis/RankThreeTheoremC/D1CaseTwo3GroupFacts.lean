module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Comp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverInvolve
import CFSG.RankThree.PartOne.K159.AutSzIso

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem caseTwoGroupFacts_of_certificates :
    CaseTwoGroupFacts := by
  intro p L _ _ hL
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd | hd, -⟩ := hL
    · exact Or.inl hd.1
    · exact Or.inr hd.1
  rcases hp35 with rfl | rfl
  · obtain ⟨h504, -, -⟩ := KFactProofs.ThreeCover.l28_facts hL
    rw [h504]
    exact ⟨by norm_num, fun _ => by norm_num, fun h => absurd h (by norm_num)⟩
  · obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hL
    rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
    · omega
    · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
      have hcard := (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie (S := L)
        ⟨hv, ⟨e⟩⟩).card
      rw [hcard]
      exact ⟨by norm_num, fun h => absurd h (by norm_num), fun _ => by norm_num⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
