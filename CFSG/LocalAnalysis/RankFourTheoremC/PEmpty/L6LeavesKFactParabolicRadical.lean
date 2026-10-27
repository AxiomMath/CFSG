module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicRadicalReduce
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Reduction
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.QuasithinUnique.Bridge.Over
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

namespace KPRad

theorem overgroups_of_isChevSimple_two
    {S : Type} [Group S] [Finite S] (h : IsChevSimple 2 S) : Overgroups S := by
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h with ⟨t, n, f, hm⟩ | ⟨e⟩ | h33
  · have hsimp : IsSimpleGroup S :=
      (CFSG.LieType.Catalog.lieModel_finite_simple S t n 2 f hm).2.2
    exact CFSG.Quasithin.LieOver.asLieTwo_holds.1 S hsimp
      (Or.inl ⟨t, n, f, CFSG.Blueprint.LieModel.admissible hm, hm⟩)
  · obtain ⟨e⟩ := e
    exact Overgroups.of_mulEquiv e.symm overgroups_alt_six
  · exact CertU33.overgroups_of_lieModel (.inl ⟨by simp [CFSG.Blueprint.classicalTags], h33⟩)

end KPRad

theorem kFactParabolicRadical_holds
    : KFactParabolicRadical :=
  kFactParabolicRadical_of_overgroups fun _ _ _ h => KPRad.overgroups_of_isChevSimple_two h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
