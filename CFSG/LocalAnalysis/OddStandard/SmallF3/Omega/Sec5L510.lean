module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BCase59
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartA8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma510_of (hy : Sec5B59Hyp) (l58d : Asc82Lemma58d) (f59 : Asc82Fact59)
    (f510 : Asc82Fact510) : Asc82Lemma510 := by
  intro G _ _ t L S z r B A hR
  obtain ⟨φ, hm⟩ := sec5b_model58_of l58d hR
  obtain ⟨c1, c2, c3⟩ := sec5b_case59_sets hy f510 hR hm
  obtain ⟨Alt, hAlt, hH⟩ := sec5b_heartA8 f59 hm (sec5b_tM_eq hy f510 hR hm)
  exact ⟨c1, c2, c3, Alt, hAlt, hH⟩

end CFSG.OddStandard.SmallF3.Omega
