module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.RankThree.PartOne.SEITZ10.SzMain

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

theorem finite_isSimpleGroup_cat_suzuki {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid) :
    Finite (Cat ⟨.suzuki m, hv⟩) ∧ IsSimpleGroup (Cat ⟨.suzuki m, hv⟩) := by
  have hmodel := suzukiModel_cat hv
  have hsimple := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 (2 * m + 1) hmodel).2
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, hsimple⟩

section Regime


theorem seitzExcOuterNarrowForAt_suzuki_geFive :
    SeitzExcOuterNarrowForAt IsSuzukiIndex PrimeRange.geFive :=
  seitzExcOuterNarrowForAt_of_family (c := LieTypeIndex.suzuki) (P := fun _ _ => True)
    (F := IsSuzukiIndex) (fun _ hv => finite_isSimpleGroup_cat_suzuki hv)
    (fun m => ExtSeitzAtOuterFor.of_outer
      (SEITZ2.extSeitzAtOuter_suzuki_of_pair SEITZ10.subfieldPairSz_holds m))
    (fun d p hF hQ => by
      obtain ⟨m, rfl⟩ := hF
      exact ⟨m, rfl, hQ, trivial⟩)

theorem seitzExcOuterNarrowSuzuki : SeitzExcOuterNarrowSuzuki :=
  SeitzExcOuterNarrowFor.of_three_geFive seitzExcOuterNarrowForAt_suzuki_three
    seitzExcOuterNarrowForAt_suzuki_geFive

end Regime

end CFSG.LieType.SeitzGeneration
