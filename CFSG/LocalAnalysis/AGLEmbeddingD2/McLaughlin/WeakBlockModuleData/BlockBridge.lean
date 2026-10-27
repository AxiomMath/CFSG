module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem le_normalizer_blockV (S L : Subgroup G) :
    L ≤ Subgroup.normalizer (blockV S L : Set G) :=
  le_sup_left.trans (le_normalizer_of_characteristic_pCoreOf
    (QuasithinUnique.Setup.omegaOneCenterOf_le _)
    (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _))

theorem isElemAbelian_blockV (S L : Subgroup G) : IsElemAbelian 2 (blockV S L) :=
  isElemAbelian_omegaOneCenterOf _

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
