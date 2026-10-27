module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Main
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeCases
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverWeakGen

public section

namespace GL83.I243

open CFSG CFSG.Open TauCeti CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs
  CFSG.AGLEmbedding.KFactProofs.ThreeWeak
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)

section


theorem threeCoverTable_holds (hSpor : SporadicMultipliers) : ThreeCoverTable := by
  intro i hi K _ _ hq hZ hZp hZc ⟨e⟩ T
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | ⟨q, hv, hq3, rfl⟩ | ⟨q, hv, hq3, rfl⟩ |
    ⟨q, hv, hq3, rfl⟩
  · exact (weakCore_McL hq hZ hZp hZc e T).1
  · exact (weakCore_Suz hq hZ hZp hZc e T).1
  · exact (weakCore_Fi22 hq hZ hZp hZc e T).1
  · exact (weakCore_Fi24 hq hZ hZp hZc e T).1
  · obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
        (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    exact (weakCore_rank_of_coverWeakGen hq hZ hZp hZc (e.trans b.symm) j3CoverWeakGenThree T).1
  · exact (CoverThree.onan_case hSpor hq hZ hZp hZc e T).1
  · exact (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (weakGenU43 q hv hq3) T).1
  · exact (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (weakGenO73 q hv hq3) T).1
  · exact (weakCore_rank_of_coverWeakGen hq hZ hZp hZc e (weakGenG23 q hv hq3) T).1

end

end GL83.I243
