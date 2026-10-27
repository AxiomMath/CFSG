module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddBasic
public import CFSG.Blueprint.NativeSporadic
import CFSG.RankThree.PartTwo.Census.Sporadic.McL
import CFSG.RankThree.PartTwo.Census.Sporadic.Ly
import CFSG.RankThree.PartTwo.Census.Sporadic.Suz
import CFSG.RankThree.PartTwo.Census.Sporadic.ON
import CFSG.RankThree.PartTwo.Census.Sporadic.Co3
import CFSG.RankThree.PartTwo.Census.Sporadic.HN

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Assembly CFSG.RankThree.PartTwo.Census CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem Standing.false_of_McL
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .McL) : False := by
  have : Finite NativeSporadic.McL := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_McL

theorem Standing.false_of_Ly
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .Ly) : False := by
  have : Finite NativeSporadic.Ly := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Ly

theorem Standing.false_of_Suz
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .Suz) : False := by
  have : Finite NativeSporadic.Suz := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Suz

theorem Standing.false_of_ON
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .ONan) : False := by
  have : Finite NativeSporadic.ON := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_ON

theorem Standing.false_of_Co3
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .Co3) : False := by
  have : Finite NativeSporadic.Co3 := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_Co3

theorem Standing.false_of_HN
    (hS : Standing G) (e : G ≃* NativeSporadic.Carrier .HN) : False := by
  have : Finite NativeSporadic.HN := Finite.of_equiv G e.toEquiv
  exact hS.false_of_not_isCharTwoType e not_isCharTwoType_HN

end CFSG.LocalAnalysis.RankThreeUC
