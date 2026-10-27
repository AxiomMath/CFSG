module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4ConjNormFinal
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4RankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Final
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L28
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma42
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Final
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieFinal
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGame

public section

namespace CFSG.ComponentClassification.RankTwoFoundation

open CFSG.ComponentClassification.AS76b

theorem asc75Theorem4_of_endgame
    (hE : Asc75T4.StepEndgame) : Asc75Theorem4 :=
  Asc75T4.asc75Theorem4_of_steps AschbacherTheorem3.theorem_3_holds
    AschbacherTheorem5.conclusion_holds Asc75T4.stepConjNormalizer hE
    (Asc75T4.stepRankOne AschbacherTheorem3.theorem_3_holds)

theorem asc76Theorem2_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Asc76Theorem2 := by
  have h22 := Asc76.asc76Lemma22 AschbacherTheorem3.theorem_3_holds
  have h75 := asc75Theorem4_of_endgame hE
  exact Asc76.Sec5.asc76Theorem2_of h22 h75 (Asc76X.asc76Theorem4_of_lemma28 Asc76.asc76Lemma28)
    (Asc76.Sec4.asc76Theorem3Large_of_theorem5 (Asc76.Sec4.asc76Theorem5_of_thm5Flat h22
      (Asc76X.asc76Theorem1_of_lemma28 Asc76.asc76Lemma28) h75 hflat)) hF

theorem lemma32_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Lemma32 :=
  lemma32_of_asc76Theorem2 (asc76Theorem2_of_steps hE hflat hF)

theorem lemma33One_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Lemma33One :=
  lemma33One_of_asc76Theorem2 (asc76Theorem2_of_steps hE hflat hF)

theorem lemma33Two_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Lemma33Two :=
  lemma33Two_of_asc76Theorem2 (asc76Theorem2_of_steps hE hflat hF) (asc75Theorem4_of_endgame hE)
    asc08Lemma34

theorem lemma33Three_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Lemma33Three :=
  lemma33Three_of_asc76Theorem2 (asc76Theorem2_of_steps hE hflat hF)

theorem section3Config_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : Section3Config :=
  section3Config_of_asc76Theorem2 (asc76Theorem2_of_steps hE hflat hF)
    (asc75Theorem4_of_endgame hE) asc08Lemma34

theorem rankTwoOddLieStandard_of_steps
    (hE : Asc75T4.StepEndgame) (hflat : Asc76.Sec4.Thm5Flat)
    (hF : Asc76.Asc76Theorem3Four) : RankTwoStandard.RankTwoOddLieStandard :=
  RankTwoOddLie.rankTwoOddLieStandard_of_foundation (asc76Theorem2_of_steps hE hflat hF)
    (asc75Theorem4_of_endgame hE)

theorem asc75Theorem4
    : Asc75Theorem4 :=
  asc75Theorem4_of_endgame Asc75T4.stepEndgame

end CFSG.ComponentClassification.RankTwoFoundation
