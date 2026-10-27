module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEnd
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoGeneral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixFinal
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchur
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1
public import CFSG.Goldschmidt.Final

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem footeTheoremTwoTwo_holds : FooteTheoremTwoTwo := fun Q htight hodd =>
  AschbacherStrongEmbedding.theorem_2_part_two
    CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
    AschbacherStrongEmbedding.benderDoubleCoverRigidity Q htight hodd

theorem footeBenderSolvable_holds : FooteBenderSolvable :=
  AschbacherStrongEmbedding.strongly_embedded_solvable

theorem aschbacherTheorem3_holds : AschbacherTheorem3.Theorem3Statement :=
  AschbacherTheorem3.theorem_3_of_theorem_4_8
    (AschbacherTheorem3.theorem_4_8_of_F2 CFSG.Goldschmidt.topStatement
      WalterSchur.walter_schur_two_part_holds
      (AschbacherTheorem3.lemma_4_6 CFSG.Goldschmidt.topStatement
        WalterSchur.theorem3KnownGroupFacts_holds))

theorem false_of_footeNoEscape_closed (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) {M : Subgroup G}
    (hM : IsFooteM L M) (hne : FooteNoEscape M) : False :=
  false_of_footeNoEscape h h47 hST hA5 hE8 hK hcalc hFI footeTheoremTwoTwo_holds
    footeBenderSolvable_holds aschbacherTheorem3_holds hM hne

end CFSG.ComponentClassification.FooteLit
