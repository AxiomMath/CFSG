module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Lemma96
public import CFSG.LocalAnalysis.GLTheoremB.Prop95FixedFacts
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NearSolvTwo
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L2Three
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAb
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Lemma97
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Lemma97Ab
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Ii
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Iii
public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyMain

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts


theorem lemma97_holds : Lemma97 :=
  lemma97_of lemma97Ab_holds
    (lemma97NonAb_of lemma96_holds fixedOddFact_holds
      (fixedTwoFacts_of nearSolvableTwoFacts_holds l2ThreeNotChevTwoOrAlt_holds))

theorem prop95_of_iv (hC : Prop95IvChev) (hA : Prop95IvAlt) : Prop95 :=
  prop95_of lemma96_holds lemma97_holds (prop95i_of lemma97_holds) prop95ii_holds
    prop95iii_holds hC hA

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
