module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartOne.SEITZ8.D4TwoMain

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Even


theorem extSeitzAtOuterFor_trialityD4_even {q : PrimePower} (hq : q.p = 2) :
    ExtSeitzAtOuterFor (.trialityD4 q) fun _ => True :=
  ExtSeitzAtOuterFor.of_outer (SEITZ2.extSeitzAtOuter_trialityD4_of_pair
    (SEITZ8.subfieldPairD4_of_two SEITZ8.subfieldPairD4Two_holds) hq)

theorem seitzExcOuterNarrowForAt_triality_even :
    SeitzExcOuterNarrowForAt IsTrialityIndex fun d p =>
      5 ≤ p ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2 :=
  seitzExcOuterNarrowForAt_of_family (c := LieTypeIndex.trialityD4) (P := fun q _ => q.p = 2)
    (F := IsTrialityIndex) (fun _ hv => finite_isSimpleGroup_cat_trialityD4 hv)
    (fun q K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hout =>
      extSeitzAtOuterFor_trialityD4_even hP K hnab hiso p hp hp5 hpd trivial E hE hcard hout)
    (fun d p _ hQ => by
      obtain ⟨hp5, q, rfl, hq⟩ := hQ
      exact ⟨q, rfl, hp5, hq⟩)

end Even

@[expose] def SeitzExcOuterNarrowTrialityOdd : Prop :=
  SeitzExcOuterNarrowForAt IsTrialityIndex fun d p =>
    5 ≤ p ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2

@[expose] def SeitzExcOuterNarrowTrialityThree : Prop :=
  SeitzExcOuterNarrowForAt IsTrialityIndex PrimeRange.three

section Assembly


theorem seitzExcOuterNarrowFor_triality_of_residuals (hodd : SeitzExcOuterNarrowTrialityOdd)
    (h3 : SeitzExcOuterNarrowTrialityThree) : SeitzExcOuterNarrowTriality :=
  SeitzExcOuterNarrowFor.of_three_geFive h3
    (SeitzExcOuterNarrowForAt.of_cover (fun d p _ _ hT hQ => by
      obtain ⟨q, rfl⟩ := hT
      by_cases h : q.p = 2
      · exact Or.inl ⟨hQ, q, rfl, h⟩
      · exact Or.inr ⟨hQ, q, rfl, h⟩) seitzExcOuterNarrowForAt_triality_even hodd)

end Assembly

end CFSG.LieType.SeitzGeneration
