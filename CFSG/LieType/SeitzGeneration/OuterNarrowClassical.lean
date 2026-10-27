module

public import CFSG.LieType.SeitzGeneration.OuterNarrowThree
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LieType.SeitzGeneration.OuterSUCat
public import CFSG.LieType.SeitzGeneration.OuterSpCat

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2


theorem seitzOuterLowNarrow_of_pairs (hSL : SubfieldPairSLLt) (hSp : SubfieldPairSpOdd)
    (hSU : SubfieldPairSUOdd) (hOH : OuterHeisCore) (hUH : UnitaryHeisCore)
    (hUOH : UnitaryOuterHeisCore)
    (hO : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      IsOrthogonalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)) : SeitzOuterLowNarrow := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hcl, hD4⟩
  have hrange : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases (isClassicalIndex_iff hrange).1 hcl with hlin | hun | hsp | hor
  · by_cases hx : p = 3 ∧ ∃ q, d = .A 2 q ∧ 3 ∣ q.card - 1
    · exact seitzOuter_A2_three hOH ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hlin, hx⟩
    · exact seitzOuter_linear hSL ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hlin, hx⟩
  · by_cases hx : p = 3 ∧ ∃ q, d = .twistedA 2 q ∧ 3 ∣ q.card + 1
    · exact seitzOuter_twistedA2_three hUH hUOH ⟨d, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hout, hs, hun, hx⟩
    · exact seitzOuter_unitary hSU ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs.1, hun, hx⟩
  · exact seitzOuter_symplectic hSp ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hsp⟩
  · exact hO ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, hor, hD4⟩

end CFSG.LieType.SeitzGeneration
