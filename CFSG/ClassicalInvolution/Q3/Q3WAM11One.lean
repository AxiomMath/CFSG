module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W


@[expose] def M11OneInput : Prop := ShapePiece3 1 CompData.m11


theorem pieceM11₃_of_input (h3 : OddThreeFreeInput) (h1 : M11OneInput) : PieceM11₃ :=
  pieceM11₃_of_one h3 h1

end CFSG.ClassicalInvolution.Q3.Q3W
