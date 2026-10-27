module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4HeisLocalEq
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Transfer

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d2HeisLocalAt_J4_of_normMax
    (hmax : NormMax (Q11Sylow : Subgroup J)) :
    D2HeisLocalAt (.sporadic .J4) fun p => p = 11 :=
  d2HeisLocalAt_J4_of_local Q11Sylow hmax heisLocalEq_Q11Sylow

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
