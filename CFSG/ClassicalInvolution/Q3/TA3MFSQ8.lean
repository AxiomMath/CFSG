module

public import CFSG.ClassicalInvolution.Q3.TA3TypeCQ8
public import CFSG.ClassicalInvolution.Q3.TA3LiftQ8
public import CFSG.ClassicalInvolution.Q3.TA3SmallOddLieS

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.GH74.GLS.Balance
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

section Base


theorem residualCNormal_of_partsQ8 (hlarge : TightHasMember3LargeBelowQ8)
    (hsmall : SmallRangeOuter) : ResidualCNormal := by
  intro Y _ _ hB z L T hS hfree hC Q hQ
  obtain ⟨hsimp, hnab, R, S, t, hD, hq8⟩ := typeCNormalDatumQ8_proved Y z L T hS hC Q hQ
  have : T.Normal := hS.normal
  obtain ⟨-, h3⟩ := odd_index_of_memberIndex_eq_three hS.sup hC
  have hlt : Nat.card T < Nat.card Y := by
    have hmul := T.card_mul_index
    have hpos : 0 < Nat.card T := Nat.card_pos
    have hidx : 3 ≤ T.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h3
    nlinarith
  by_cases hF : TwoSubgroupsFourGenerated (genFittingFStar ↥T)
  · exact hsmall Y T hsimp hnab hS.cent hF hfree h3 ⟨R, S, t, hD⟩
  · obtain ⟨hFs, hFnab⟩ := genFittingFStar_simple ↥T hnab
    obtain ⟨z', J, hJ⟩ := hlarge (Nat.card Y) hB ↥T hlt hFnab hF R S t hD hq8
    exact hfree z' J hJ

theorem memberFreeSocleOuter3_of_partsQ8 (hbal : SolvableL2PrimeBalance)
    (hlarge : TightHasMember3LargeBelowQ8) (hsmall : SmallRangeOuter) (hframe : ResidualCFrame) :
    Q3T.MemberFreeSocleOuter3 :=
  memberFreeSocleOuter3_of_residualC hbal (residualCNormal_of_partsQ8 hlarge hsmall) hframe

end Base

section Gh74


theorem memberFreeSocleOuter3_of_gh74Q8 (hbal : SolvableL2PrimeBalance)
    (hGH : GH74SectionalModels) (hlarge : TightHasMember3LargeBelowQ8)
    (hodd : SmallOddLieTightMemberS) (hframe : ResidualCFrame) : Q3T.MemberFreeSocleOuter3 :=
  memberFreeSocleOuter3_of_partsQ8 hbal hlarge (smallRangeOuter_of_partsS hGH hodd) hframe

end Gh74

end CFSG.ClassicalInvolution.Q3.TA3
