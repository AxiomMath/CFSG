module

public import CFSG.LieType.SeitzGeneration.ClassicalSeitzStatus
public import CFSG.LieType.SeitzGeneration.ClassicalNonabAssembly
public import CFSG.LieType.SeitzGeneration.OrthManyMaster
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverTransfer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace GL83.I243

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcWideThree TauCeti

section Planes

theorem seitzPlanes_classical :
    SeitzPlanes fun d p _ => IsClassicalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1) := by
  intro d p hp hp2 hpd hex E hE hc ⟨hcl, hD4⟩
  by_cases hi : InnerPlane d p E
  · rcases PrimeRange.eq_three_or_five_le hp hp2 with hp3 | hp5
    · exact seitzInnerThreeClassical_holds d p hp hp2 hpd hex E hE hc ⟨hi, hp3, hcl⟩
    · exact seitzInnerClassicalFive_of_lift (seitzInnerClassicalAb_of_leaves unitarySUNontoral
        orthogonalOddPlanes orthogonalPlusPlanes orthogonalMinusPlanes)
        seitzInnerClassicalNonab_holds d p hp hp2 hpd hex E hE hc ⟨hi, hp5, hcl⟩
  · exact seitzOuterClassical_holds d p hp hp2 hpd hex E hE hc ⟨hi, hcl, hD4⟩

end Planes

end GL83.I243
