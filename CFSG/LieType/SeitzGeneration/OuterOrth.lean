module

public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LieType.SeitzGeneration.ThreeIndepOrth

public section

namespace CFSG.LieType.SeitzGeneration

theorem seitzOuter_orthogonal (hpair : SubfieldPairOmega) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsOrthogonalIndex d.1 ∧
      ¬ (p = 3 ∧ IsDFourIndex d.1) := by
  rintro d p hp hp2 hpd hex E hE hc ⟨hout, hrk, horth, -⟩
  by_cases h5 : 5 ≤ p
  · exact seitzOuter_orthogonal_five hpair d p hp hp2 hpd hex E hE hc ⟨hout, h5, horth⟩
  · have hp3 : p = 3 ∨ p = 4 := by
      have := hp.two_le
      omega
    rcases hp3 with rfl | rfl
    · exact absurd hrk (not_rankLE2_orthogonal_three d horth)
    · exact absurd hp (by norm_num)

theorem seitzOuter_orthogonal_narrow (hpair : SubfieldPairOmega) :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ IsOrthogonalIndex d.1 ∧
      ¬ (p = 3 ∧ IsDFourIndex d.1) :=
  SeitzPlanes.mono (fun _ _ _ h => ⟨h.1, h.2.1.1, h.2.2⟩) (seitzOuter_orthogonal hpair)

end CFSG.LieType.SeitzGeneration
