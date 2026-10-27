module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin

theorem blockV_le_normalizer_of_pair {G : Type} [Group G] [Finite G] {M H R L : Subgroup G}
    (h : AGLPair 3 M H R) (h86 : Asc81bEightSix) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∀ v ∈ blockV (pCoreOf 2 H) L, ∀ l ∈ L, v * l * v⁻¹ ∈ L := by
  intro v hv l hl
  have hSL := (h.weakSBlock_asc81bHyp h86 hL).1
  have hvT : v ∈ pCoreOf 2 (L ⊔ pCoreOf 2 H) := QuasithinUnique.Setup.omegaOneCenterOf_le _ hv
  have hvS : v ∈ pCoreOf 2 H := (h.blockV_facts h86 hL).2.1 hvT
  exact (Subgroup.mem_normalizer_iff.mp (hSL hvS) l).mp hl

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
