module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.SEITZ2.G2F2Main

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Proved


theorem extSeitzAtOuterFor_G2_proved (q : PrimePower) :
    ExtSeitzAtOuterFor (.G2 q) fun _ => q.p = 2 ∨ (q.p ≠ 2 ∧ q.exponent = 1) :=
  fun K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hout => by
    rcases hP with h2 | ⟨h2, he⟩
    · exact SEITZ2.extSeitzAtOuter_G2_of_pair
        (SEITZ2.subfieldPairG2_of_f2 SEITZ2.subfieldPairG2F2) h2 K hnab hiso p hp hp5 hpd E hE
        hcard hout
    · exact extSeitzAtOuter_G2_odd h2 he K hnab hiso p hp hp5 hpd E hE hcard hout

end Proved

section Regime


theorem seitzExcOuterNarrowForAt_G2_proved :
    SeitzExcOuterNarrowForAt IsG2Index fun d p =>
      ∃ q : PrimePower, d = .G2 q ∧ 5 ≤ p ∧ (q.p = 2 ∨ (q.p ≠ 2 ∧ q.exponent = 1)) :=
  seitzExcOuterNarrowForAt_family (c := LieTypeIndex.G2)
    (P := fun q _ => q.p = 2 ∨ (q.p ≠ 2 ∧ q.exponent = 1))
    (fun _ hv => finite_isSimpleGroup_cat_G2 hv) extSeitzAtOuterFor_G2_proved

@[expose] def SeitzExcOuterNarrowG2OddPower : Prop :=
  SeitzExcOuterNarrowForAt IsG2Index fun d p =>
    5 ≤ p ∧ ∃ q : PrimePower, d = .G2 q ∧ q.p ≠ 2 ∧ q.exponent ≠ 1

@[expose] def SeitzExcOuterNarrowG2Three : Prop :=
  SeitzExcOuterNarrowForAt IsG2Index PrimeRange.three

theorem seitzExcOuterNarrowFor_G2_of_residuals (h5 : SeitzExcOuterNarrowG2OddPower)
    (h3 : SeitzExcOuterNarrowG2Three) : SeitzExcOuterNarrowG2 :=
  SeitzExcOuterNarrowFor.of_three_geFive h3
    (SeitzExcOuterNarrowForAt.of_cover (fun d p _ _ hG hQ => by
      obtain ⟨q, rfl⟩ := hG
      by_cases h : q.p = 2
      · exact Or.inl ⟨q, rfl, hQ, Or.inl h⟩
      by_cases he : q.exponent = 1
      · exact Or.inl ⟨q, rfl, hQ, Or.inr ⟨h, he⟩⟩
      · exact Or.inr ⟨hQ, q, rfl, h, he⟩) seitzExcOuterNarrowForAt_G2_proved h5)

end Regime

end CFSG.LieType.SeitzGeneration
