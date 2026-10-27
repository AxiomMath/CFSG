module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Orth
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def oddProjEquiv (n : ℕ) (hd : 0 < 2 * n + 1) :
    StatedProj (StatedOmega (StatedQuadOdd n K)) ≃* ProjOrthDerived (coordinateQuadOdd n K) :=
  (statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n K) (coe_quadOdd n K)).trans
    (coordBridge (coordinateQuadOdd n K) hd)

@[expose] noncomputable def plusProjEquiv (n : ℕ) (hd : 0 < 2 * n) :
    StatedProj (StatedOmega (StatedQuadPlus n K)) ≃* ProjOrthDerived (coordinateQuadPlus n K) :=
  (statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)).trans
    (coordBridge (coordinateQuadPlus n K) hd)

@[expose] noncomputable def minusProjEquiv (n : ℕ) (hn : 1 ≤ n) (b c : K)
    (hd : 0 < 2 * n) :
    StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      ProjOrthDerived (coordinateQuadMinus n K hn b c) :=
  (statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n K b c)
    (coe_quadMinus n K b c)).trans (coordBridge (coordinateQuadMinus n K hn b c) hd)

theorem ringChar_ne_two_of_card_eq_three (hK3 : Nat.card K = 3) : ringChar K ≠ 2 := by
  intro h
  have h3 : ((2 : ℕ) : K) = 0 := (ringChar.spec K 2).mpr (by rw [h])
  exact two_ne_zero_of_card_eq_three hK3 (by simpa using h3)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
