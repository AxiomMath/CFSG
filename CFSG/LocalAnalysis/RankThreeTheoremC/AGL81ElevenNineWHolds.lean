module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineFieldIndexWDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWSymp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWOrth
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWGTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

theorem kFactCompParabFieldIndexWAt_of_families {p : ℕ}
    (hA : FieldIndexOnPW p (IsLieOf IdxA))
    (h2A : FieldIndexOnPW p (IsLieOf IdxTwistedA)) (hB : FieldIndexOnPW p (IsLieOf IdxB))
    (hD : FieldIndexOnPW p (IsLieOf IdxD)) (h2D : FieldIndexOnPW p (IsLieOf IdxTwistedD))
    (hG : FieldIndexOnPW p (IsLieOf IdxG2)) (hS : FieldIndexOnPW p IsSmallTwoOrG2) :
    KFactCompParabFieldIndexWAt p := by
  intro Y _ _ L P hCP hLn hrank h3 hrk a ha3 haN hout
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    h2A Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hB Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hD Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    h2D Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hG Y L P hCP h hLn hrank h3 hrk a ha3 haN hout,
    hS Y L P hCP h hLn hrank h3 hrk a ha3 haN hout]

theorem kFactCompParabFieldIndexWAt_of_griess (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) : KFactCompParabFieldIndexWAt p :=
  kFactCompParabFieldIndexWAt_of_families (fieldIndexOnPW_linear p hGA) (fieldIndexOnPW_unitary p)
    (fieldIndexOnPW_symp p hGA) (fieldIndexOnPW_orthPlus p hGA) (fieldIndexOnPW_orthMinus p hGA)
    (fieldIndexOnPW_g2 p hGA) (fieldIndexOnPW_small p hGA)

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
