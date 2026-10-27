module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntStandard
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerBridge

public section

namespace CFSG.EvenSmallLie.UnitarySix

theorem childU6Cover :
    ChildU6Cover := by
  intro G _ _ L hset hZ hZ2 hQ
  have : IsSimpleGroup G := hset.simple
  have h2 : Nat.card (Subgroup.center L) = 2 := std_card_center_eq_two hset hZ hZ2 hQ
  obtain ⟨t, p, -, -, H⟩ := Hunt.std_exists_hyp hset h2 hQ
  exact Fischer.fi22_of_huntHyp H

end CFSG.EvenSmallLie.UnitarySix
