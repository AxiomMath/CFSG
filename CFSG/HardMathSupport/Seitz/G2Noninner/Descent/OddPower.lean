module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddThree
public import CFSG.LieType.SeitzGeneration.ExcOuterG2

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2
  CFSG.LieType.SeitzGeneration TauCeti

section Index

theorem extSeitzAtOuterFor_G2_oddPower (hpair : SubfieldPairG2Odd) (q : PrimePower) :
    ExtSeitzAtOuterFor (.G2 q) fun _ => q.p ≠ 2 ∧ q.exponent ≠ 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hout
  obtain ⟨hq2, -⟩ := hP
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := exists_adjointG2_model hiso
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hd : FieldAutData (adjointGroup .G2 X) p := by
    by_cases h3 : q.p = 3
    · exact fieldAutData_G2_three hpair hf (by rw [hX, h3]) hp hp5
    · exact fieldAutData_G2_odd_ne_three hpair q.prime_p hq2 h3 hf hX hp hp5
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp (hd.of_mulEquiv e hp) E hcard hout

end Index

section Regime

theorem seitzExcOuterNarrowG2OddPower_of_pair (hpair : SubfieldPairG2Odd) :
    SeitzExcOuterNarrowG2OddPower := by
  have h := seitzExcOuterNarrowForAt_family (c := LieTypeIndex.G2)
    (P := fun q _ => q.p ≠ 2 ∧ q.exponent ≠ 1)
    (fun _ hv => finite_isSimpleGroup_cat_G2 hv) (extSeitzAtOuterFor_G2_oddPower hpair)
  exact SeitzExcOuterNarrowForAt.mono
    (fun _ _ ⟨h5, q, hd, hq⟩ => ⟨q, hd, h5, hq⟩) h

end Regime

end CFSG.HardMathSupport.Seitz.G2Noninner
