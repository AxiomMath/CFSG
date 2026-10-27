module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Proved


theorem seitzExcAnisotropicForAt_F4_two :
    SeitzExcAnisotropicForAt IsF4Index fun d p =>
      5 ≤ p ∧ ∃ q : PrimePower, d = .F4 q ∧ q.p = 2 ∧ q.exponent = 1 :=
  seitzExcAnisotropicForAt_of_family (c := LieTypeIndex.F4)
    (P := fun q _ => q.p = 2 ∧ q.exponent = 1) (F := IsF4Index)
    (fun _ hv => finite_isSimpleGroup_cat_F4 hv)
    (fun q K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hin =>
      SEITZX.extSeitzAtInner_F4_two q hP.1 hP.2 K hnab hiso p hp hp5 hpd E hE hcard hin)
    (fun d p _ hQ => by
      obtain ⟨hp5, q, rfl, hq⟩ := hQ
      exact ⟨q, rfl, hp5, hq⟩)

theorem seitzExcOuterNarrowForAt_F4_two :
    SeitzExcOuterNarrowForAt IsF4Index fun d p =>
      5 ≤ p ∧ ∃ q : PrimePower, d = .F4 q ∧ q.p = 2 ∧ q.exponent = 1 :=
  seitzExcOuterNarrowForAt_of_family (c := LieTypeIndex.F4)
    (P := fun q _ => q.p = 2 ∧ q.exponent = 1) (F := IsF4Index)
    (fun _ hv => finite_isSimpleGroup_cat_F4 hv)
    (fun q K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hout =>
      extSeitzAtOuter_F4_two hP.1 hP.2 K hnab hiso p hp hp5 hpd E hE hcard hout)
    (fun d p _ hQ => by
      obtain ⟨hp5, q, rfl, hq⟩ := hQ
      exact ⟨q, rfl, hp5, hq⟩)

end Proved

@[expose] def SeitzExcAnisotropicF4Big : Prop :=
  SeitzExcAnisotropicForAt IsF4Index fun d p =>
    5 ≤ p ∧ ∃ q : PrimePower, d = .F4 q ∧ ¬ (q.p = 2 ∧ q.exponent = 1)

@[expose] def SeitzExcAnisotropicF4Three : Prop :=
  SeitzExcAnisotropicForAt IsF4Index PrimeRange.three

@[expose] def SeitzExcOuterNarrowF4Big : Prop :=
  SeitzExcOuterNarrowForAt IsF4Index fun d p =>
    5 ≤ p ∧ ∃ q : PrimePower, d = .F4 q ∧ ¬ (q.p = 2 ∧ q.exponent = 1)

@[expose] def SeitzExcOuterNarrowF4Three : Prop :=
  SeitzExcOuterNarrowForAt IsF4Index PrimeRange.three

section Assembly


theorem seitzExcAnisotropicFor_F4_of_residuals (hbig : SeitzExcAnisotropicF4Big)
    (h3 : SeitzExcAnisotropicF4Three) : SeitzExcAnisotropicF4 :=
  SeitzExcAnisotropicFor.of_three_geFive h3
    (SeitzExcAnisotropicForAt.of_cover (fun d p _ _ hF hQ => by
      obtain ⟨q, rfl⟩ := hF
      by_cases h : q.p = 2 ∧ q.exponent = 1
      · exact Or.inl ⟨hQ, q, rfl, h⟩
      · exact Or.inr ⟨hQ, q, rfl, h⟩) seitzExcAnisotropicForAt_F4_two hbig)

theorem seitzExcOuterNarrowFor_F4_of_residuals (hbig : SeitzExcOuterNarrowF4Big)
    (h3 : SeitzExcOuterNarrowF4Three) : SeitzExcOuterNarrowF4 :=
  SeitzExcOuterNarrowFor.of_three_geFive h3
    (SeitzExcOuterNarrowForAt.of_cover (fun d p _ _ hF hQ => by
      obtain ⟨q, rfl⟩ := hF
      by_cases h : q.p = 2 ∧ q.exponent = 1
      · exact Or.inl ⟨hQ, q, rfl, h⟩
      · exact Or.inr ⟨hQ, q, rfl, h⟩) seitzExcOuterNarrowForAt_F4_two hbig)

end Assembly

end CFSG.LieType.SeitzGeneration
