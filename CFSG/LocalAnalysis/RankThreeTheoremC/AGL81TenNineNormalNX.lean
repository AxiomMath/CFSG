module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

@[expose] def Asc81bASevenPLRankNX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) →
    ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (normalizer (S : Set G) ⊓ L) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
