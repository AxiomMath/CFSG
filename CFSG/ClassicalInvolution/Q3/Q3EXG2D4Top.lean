module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Main
public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Gen
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FMain
public import CFSG.ClassicalInvolution.Q3.Q3EXMain2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank


theorem rowShapeExoticG2D43 (h3 : OddThreeFreeInput) :
    RowPiece3 ShapeExoticG2D43 := by
  rintro a t n ⟨-, ht, hadm⟩ G _ _ _ hnab K z hR hshape
  have hgen : EX.GenFact3 (CompData.model t n) := by
    rcases ht with rfl | rfl
    · exact EX.genFact3_g2 hadm
    · exact EX.genFact3_td4 hadm
  exact (EX.false_of_g2d4_exotic hnab ⟨hR, h3 G K z hR, ht, hadm, hshape⟩
    (EX.G2D4Facts3.of_model ht hadm hgen)).elim

theorem pieceExotic₃_of_formal (h3 : OddThreeFreeInput)
    (hrows : RowPiece3 ShapeTable3) (hA1 : PieceAllA1₃) (hM11 : PieceM11₃) : PieceExotic₃ :=
  pieceExotic₃_of_g2d4_d4 h3 hrows hA1 hM11 (rowShapeExoticG2D43 h3) (rowShapeExoticD43 h3)

end CFSG.ClassicalInvolution.Q3.Q3W
