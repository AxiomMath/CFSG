module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartOne.SEITZRF.Two

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Proved


theorem seitzExcOuterNarrowForAt_reeF4_geFive :
    SeitzExcOuterNarrowForAt IsReeF4Index PrimeRange.geFive :=
  seitzExcOuterNarrowForAt_of_family (c := LieTypeIndex.reeF4) (P := fun _ _ => True)
    (F := IsReeF4Index) (fun _ hv => finite_isSimpleGroup_cat_reeF4 hv)
    (fun m => ExtSeitzAtOuterFor.of_outer
      (SEITZ2.extSeitzAtOuter_reeF4_of_pair SEITZRF.subfieldPairReeF4_holds m))
    (fun d p hF hQ => by
      obtain ⟨m, rfl⟩ := hF
      exact ⟨m, rfl, hQ, trivial⟩)

end Proved

@[expose] def SeitzExcOuterNarrowReeF4Three : Prop :=
  SeitzExcOuterNarrowForAt IsReeF4Index PrimeRange.three

section Assembly


theorem seitzExcOuterNarrowFor_reeF4_of_three (h3 : SeitzExcOuterNarrowReeF4Three) :
    SeitzExcOuterNarrowReeF4 :=
  SeitzExcOuterNarrowFor.of_three_geFive h3 seitzExcOuterNarrowForAt_reeF4_geFive

end Assembly

end CFSG.LieType.SeitzGeneration
