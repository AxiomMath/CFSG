module

public import CFSG.ClassicalInvolution.Q3.Q3WASThree

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W


theorem chainPiece3SLs_of_two (h3 : OddThreeFreeInput) (h2 : ChainRow3 2) : ChainPiece3SLs := by
  intro G _ _ _ hnab K z hR m hm2 hm4 hshape
  obtain rfl | rfl | rfl : m = 2 ∨ m = 3 ∨ m = 4 := by omega
  · exact h2 G hnab K z hR hshape
  · exact chainRow3_three h3 G hnab K z hR hshape
  · exact chainRow3_four h3 G hnab K z hR hshape

theorem piece3SLs_proved (h3 : OddThreeFreeInput) (h2 : ChainRow3 2) : Piece3SLs :=
  piece3SLs_of_chain h3 (chainPiece3SLs_of_two h3 h2)

end CFSG.ClassicalInvolution.Q3.Q3W
