module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem isDoubleCoverOfAlt_of_quot_bot {C : Type} [Group C] {n : ℕ} (hbot : pPrimeCore 2 C = ⊥)
    (h : IsDoubleCoverOfAlt (C ⧸ pPrimeCore 2 C) n) : IsDoubleCoverOfAlt C n := by
  let e : C ⧸ pPrimeCore 2 C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e h

end CFSG.OddStandard.Solomon75
