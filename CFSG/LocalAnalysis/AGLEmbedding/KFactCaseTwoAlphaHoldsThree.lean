module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoIn
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeSylow

public section

namespace CFSG.AGLEmbedding

open CFSG.Open TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.AGLEmbedding.KFactProofs.CoverFive
open CFSG.AGLEmbedding.KFactProofs.CoverThree

theorem kFactCaseTwoAlphaThree_of_coverThreeFix (h : KFactCoverThreeFix) :
    KFactCaseTwoAlphaThree := by
  intro K _ _ hK hcat hZ hZp hZc A L _ hL f hf hrank T
  rcases h K hK hcat hZ hZp hZc hrank T with ⟨hg, hz, ho⟩ | hw
  · exact Or.inl ⟨hg, hz, Or.inr ho⟩
  · exact Or.inr hw

end CFSG.AGLEmbedding
