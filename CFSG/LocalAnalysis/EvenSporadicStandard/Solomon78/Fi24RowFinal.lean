module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowAut

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Fi24 (R JR)
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row
  (fi24_equiv_P fi24_autCenterCond_P fi24_umovesCond_P)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi24_autCenterCond {Y : Type} [Group Y] (h : IsSporadic Y .Fi24Prime) :
    AutCenterCond Y := by
  obtain ⟨e⟩ := fi24_equiv_P h
  exact @AutCenterCond.of_mulEquiv ↥(JR : Subgroup R) Y _ _ e.symm
    (fi24_autCenterCond_P CFSG.Fischer.polarFacts CFSG.Sporadic.Fi22.card_fixed_involution_D
      CFSG.Sporadic.Fi22.eq_of_commute_centralizer CFSG.Sporadic.Fi24.edgeSwap_a)

theorem fi24_umovesCond {Y : Type} [Group Y] (h : IsSporadic Y .Fi24Prime) : UMovesCond Y := by
  obtain ⟨e⟩ := fi24_equiv_P h
  exact @UMovesCond.of_mulEquiv ↥(JR : Subgroup R) Y _ _ e.symm
    (fi24_umovesCond_P CFSG.Fischer.polarFacts)

end CFSG.EvenSporadicStandard.Solomon78
