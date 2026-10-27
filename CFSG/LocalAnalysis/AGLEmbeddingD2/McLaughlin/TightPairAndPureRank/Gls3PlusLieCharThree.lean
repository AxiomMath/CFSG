module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusGLB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree


theorem gls3PlusCase_lie_of_char_three (d : TauCeti.ValidLieTypeIndex)
    (h3 : d.1.characteristic = 3) (hr : ¬ IsRankOneLieIndex d.1) : Gls3PlusCase (.lie d) :=
  gls3PlusCase_of_glbCore _ fun K _ _ hs hnab he T =>
    charPGen K hs hnab d he 3 Nat.prime_three (by norm_num) h3.symm hr T

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
