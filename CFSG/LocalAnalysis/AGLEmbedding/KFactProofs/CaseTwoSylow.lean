module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.RankThree.PartOne.K159.AutSzIso

public section

namespace CFSG.AGLEmbedding

theorem card_sylow_three_of_isCaseTwoGroup {K : Type} [Group K] [Finite K]
    (hK : IsCaseTwoGroup 3 K) (T : Sylow 3 K) : Nat.card T = 9 := by
  obtain ⟨ε₀⟩ := KFactProofs.L28Local.nonempty_equiv_G8 hK
  exact KFactProofs.L28Local.card_sylow_three ε₀ T

theorem card_sylow_five_of_isCaseTwoGroup
    {K : Type} [Group K] [Finite K] (hK : IsCaseTwoGroup 5 K) (T : Sylow 5 K) :
    Nat.card T = 25 := by
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hK
  rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
  · omega
  · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
    have hcard := (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie
      (S := K) ⟨hv, ⟨e⟩⟩).card
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Sylow.card_eq_multiplicity, hcard, CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num

theorem kFactCaseTwoSylow :
    KFactCaseTwoSylow := by
  intro p K _ _ hK T
  obtain ⟨d, hd, -⟩ := id hK
  rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have h := card_sylow_three_of_isCaseTwoGroup hK T
    omega
  · have h := card_sylow_five_of_isCaseTwoGroup hK T
    omega

end CFSG.AGLEmbedding
