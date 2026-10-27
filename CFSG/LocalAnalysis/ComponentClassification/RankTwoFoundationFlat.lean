module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3Four

public section

namespace CFSG.ComponentClassification.RankTwoFoundation

open CFSG.ComponentClassification.AS76b

theorem asc76Theorem2_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Asc76Theorem2 :=
  asc76Theorem2_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem lemma32_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Lemma32 :=
  lemma32_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem lemma33One_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Lemma33One :=
  lemma33One_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem lemma33Two_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Lemma33Two :=
  lemma33Two_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem lemma33Three_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Lemma33Three :=
  lemma33Three_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem section3Config_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : Section3Config :=
  section3Config_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

theorem rankTwoOddLieStandard_of_flat
    (hflat : Asc76.Sec4.Thm5Flat) : RankTwoStandard.RankTwoOddLieStandard :=
  rankTwoOddLieStandard_of_steps Asc75T4.stepEndgame hflat Asc76X.Thm3Four.asc76Theorem3Four

end CFSG.ComponentClassification.RankTwoFoundation
