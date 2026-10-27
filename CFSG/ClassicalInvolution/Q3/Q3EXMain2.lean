module

public import CFSG.ClassicalInvolution.Q3.Q3EXMain
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

theorem shapePiece3_orth (h3 : OddThreeFreeInput) {a : ℕ} {t : StatedLieTag} {n : ℕ}
    (h : RouteD.Exotic.ShapeSingleOrth a t n) (hadm : StatedLieAdmissible t n 3 1) :
    ShapePiece3 a (CompData.model t n) := by
  obtain ⟨rfl, ht⟩ := h
  rcases ht with rfl | rfl | ⟨rfl, hn6⟩
  · have hn : 3 ≤ n := hadm.2.2.1
    by_cases h4 : 4 ≤ n
    · exact shapePiece3_odd_large h3 hadm h4
    · obtain rfl : n = 3 := by omega
      exact shapePiece3_odd_small h3
  · have hn : 4 ≤ n := hadm.2.2
    by_cases h5 : 5 ≤ n
    · exact shapePiece3_minus_large h3 hadm h5
    · obtain rfl : n = 4 := by omega
      exact shapePiece3_minus_small h3
  · have hn : 4 ≤ n := hadm.2.2
    by_cases h5 : 5 ≤ n
    · exact shapePiece3_plus_large h3 hadm h5 hn6
    · obtain rfl : n = 4 := by omega
      exact shapePiece3_plus_four h3

theorem rowShapeExoticOrth3 (h3 : OddThreeFreeInput) : RowPiece3 ShapeExoticOrth3 :=
  fun _ _ _ h => shapePiece3_orth h3 h.1 h.2

theorem pieceExotic₃_of_g2d4_d4 (h3 : OddThreeFreeInput) (hrows : RowPiece3 ShapeTable3)
    (hA1 : PieceAllA1₃) (hM11 : PieceM11₃) (hg : RowPiece3 ShapeExoticG2D43)
    (hd : RowPiece3 ShapeExoticD43) : PieceExotic₃ :=
  pieceExotic₃_of_residuals h3 hrows hA1 hM11 hg hd (rowShapeExoticOrth3 h3)

end CFSG.ClassicalInvolution.Q3.Q3W
