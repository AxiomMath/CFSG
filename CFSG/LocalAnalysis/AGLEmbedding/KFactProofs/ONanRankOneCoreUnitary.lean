module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowUnitary

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

open CFSG.AGLEmbedding.KFactProofs.SmallGamma CFSG.AGLEmbedding.KFactProofs.OneLieSylow

theorem rankOneCoreData_unitary {L : Type} [Group L] [Finite L] {p : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow p L) : RankOneCoreData L (U : Subgroup L) := by
  have hp : p.Prime := by
    obtain ⟨q, hq, -⟩ := hd
    exact hq ▸ q.prime_p
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨(smallGammaData_unitary hd h U).normalizer_le, ?_⟩
  apply normalizer_ne_top_of_card_sylow U
  rw [(card_sylow_unitary hd h U).2]
  have : 0 < (p ^ d.1.fieldExponent) ^ 3 := pow_pos (pow_pos hp.pos _) 3
  omega

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
