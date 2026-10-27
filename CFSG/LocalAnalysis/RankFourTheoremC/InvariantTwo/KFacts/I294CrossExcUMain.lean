module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcUOdd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CrossExcU

open CFSG.LocalAnalysis.ComponentInitial

theorem crossExcU_abelianProp : UnitaryAbelianProp := by
  intro ℓ f K _ _ h n p hp hp5 hpℓ
  rcases Nat.even_or_odd (unitaryOrder ℓ f p) with he | ho
  · exact unitaryAbelianAt_of_even h hp hp5 hpℓ he n
  · exact unitaryAbelianAt_of_odd h hp hp5 hpℓ ho n

theorem crossExcU_rankProp : UnitaryRankProp := by
  intro ℓ f K _ _ h n p hp hp5 hpℓ
  rcases Nat.even_or_odd (unitaryOrder ℓ f p) with he | ho
  · exact unitaryRankAt_of_even h hp hp5 hpℓ he n
  · exact unitaryRankAt_of_odd h hp hp5 hpℓ ho n

theorem crossFamUnitaryLarge : CrossFamUnitaryLarge :=
  crossFamUnitaryLarge_of_props crossExcU_rankProp crossExcU_abelianProp

end CFSG.LocalAnalysis.RankFourTheoremC
