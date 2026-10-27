module

public import CFSG.LieType.SeitzGeneration.InnerLinear
public import CFSG.LieType.SeitzGeneration.InnerSymplectic
public import CFSG.LieType.SeitzGeneration.InnerUnitary
public import CFSG.LieType.SeitzGeneration.InnerOrthogonal

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.AGLEmbeddingD2

theorem seitzInnerClassicalAb_of_leaves (hU : UnitarySUNontoral) (hO : OrthogonalOddPlanes)
    (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes) : SeitzInnerClassicalAb := by
  have hLin := seitzInnerLinear
  have hSp := seitzInnerSymplectic
  have hUni := seitzInnerUnitary_of_nontoral hU
  have hOrth := seitzInnerOrthogonal_of_leaves hO hP hM
  intro d p hp hp2 hpd hex E hE hc ⟨hinner, hp5, hcl, hlift⟩
  have hrange : d.1.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rcases (isClassicalIndex_iff hrange).1 hcl with h | h | h | h
  · exact hLin d p hp hp2 hpd hex E hE hc ⟨hinner, hp5, h, hlift⟩
  · exact hUni d p hp hp2 hpd hex E hE hc ⟨hinner, hp5, h, hlift⟩
  · exact hSp d p hp hp2 hpd hex E hE hc ⟨hinner, hp5, h⟩
  · exact hOrth d p hp hp2 hpd hex E hE hc ⟨hinner, hp5, h⟩

theorem kFactSeitzRankTwo_of_leaves (hU : UnitarySUNontoral) (hO : OrthogonalOddPlanes)
    (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes) (hN : SeitzInnerClassicalNonab)
    (hX : SeitzInnerExceptionalFive) (h3 : SeitzInnerThree) (ho : KFactSeitzRankTwoOuter) :
    KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_pieces
    (seitzInnerClassicalFive_of_lift (seitzInnerClassicalAb_of_leaves hU hO hP hM) hN) hX h3 ho

end CFSG.LieType.SeitzGeneration
