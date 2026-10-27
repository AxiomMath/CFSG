module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Out

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.Open TauCeti CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem linThreeFix_case (hGA : GriessMultipliersAllModels) (hR1 : SL3CoverGenTwoModAbFix)
    {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hZ3 := card_center_linThree hGA hK hZp hZ hd e
  exact ⟨hR1 K hK hZ3 d hd ⟨e⟩, hZ3, kFactSL3OutNormalSylow K hK d hd ⟨e⟩⟩

end CFSG.AGLEmbedding.KFactProofs.CoverThree

