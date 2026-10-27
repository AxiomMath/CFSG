module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T H K : Subgroup X}

theorem le_gnD_of_isBlock2' (hX : GNSetting X T) (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H)
    (hK : IsBlock2 H K) (hKC : ¬ K ≤ gnC T) : K ≤ gnD T :=
  le_gnD_iff.2 (commutator_pCoreOf_le_gnV_q hX hQH hK hKC)

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
