module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFlat
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Flat
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Final

public section

namespace CFSG.ComponentClassification.RankTwoFoundation

open CFSG.ComponentClassification.AS76b

theorem thm5Flat :
    Asc76.Sec4.Thm5Flat :=
  Asc76.Sec4.thm5Flat_of_b3 Asc76.Sec4.b3Conclusion

theorem asc76Theorem2 :
    Asc76Theorem2 :=
  asc76Theorem2_of_flat thm5Flat

theorem lemma32 :
    Lemma32 :=
  lemma32_of_flat thm5Flat

theorem lemma33One :
    Lemma33One :=
  lemma33One_of_flat thm5Flat

theorem lemma33Two :
    Lemma33Two :=
  lemma33Two_of_flat thm5Flat

theorem lemma33Three :
    Lemma33Three :=
  lemma33Three_of_flat thm5Flat

theorem section3Config :
    Section3Config :=
  section3Config_of_flat thm5Flat

theorem rankTwoOddLieStandard :
    RankTwoStandard.RankTwoOddLieStandard :=
  rankTwoOddLieStandard_of_flat thm5Flat

theorem asc76Theorem3Large :
    Asc76.Asc76Theorem3Large :=
  Asc76.Sec4.asc76Theorem3Large_of_theorem5 (Asc76.Sec4.asc76Theorem5_of_thm5Flat
    (Asc76.asc76Lemma22 AschbacherTheorem3.theorem_3_holds)
    (Asc76X.asc76Theorem1_of_lemma28 Asc76.asc76Lemma28) asc75Theorem4 thm5Flat)

end CFSG.ComponentClassification.RankTwoFoundation
