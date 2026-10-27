module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.LastProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagProof

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem lemma33_two_of_diag (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H]
    (hdiag : DiagData H) : Lemma33Two IsK IsL H :=
  lemma33_two_of_last IsK IsL H (noFiveAAbove_of_diag IsK IsL hdiag)

theorem lemma33_two (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H] :
    Lemma33Two IsK IsL H :=
  lemma33_two_of_diag IsK IsL H (diagData_all H)

end CFSG.EvenSporadicStandard.Induction
