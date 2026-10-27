module

public import CFSG.LieType.SeitzGeneration.OuterUnitaryWide
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.RankThree.PartTwo.KFacts

theorem unitaryOuterEightPlanes : UnitaryOuterEightPlanes := by
  intro K _ h E hE hc hD
  have hc9 : Nat.card E = 9 := by rw [hc]; norm_num
  refine planeGen_of_outer_model (psuPrimeFormEquiv h).symm ?_
  refine CFSG.RankThree.PartTwo.Sec19.planeGen_unitaryPSU_eight_of_not_le h
    (isElemAbelian_map_congr _ hE) ((card_map_congr _ E).trans hc9) ?_
  intro hle
  apply hD
  intro x hx
  obtain ⟨A, hA⟩ := hle ⟨x, hx, rfl⟩
  have h3 : MulAut.congr (psuPrimeFormEquiv h) (psuConj h A) = x := by
    have hA' : psuConj h A = (MulAut.congr (psuPrimeFormEquiv h).symm) x := hA
    rw [hA']
    ext y
    simp [MulAut.congr_apply]
  rw [← h3, congr_psuConj]
  exact ⟨_, rfl⟩

end CFSG.LieType.SeitzGeneration
