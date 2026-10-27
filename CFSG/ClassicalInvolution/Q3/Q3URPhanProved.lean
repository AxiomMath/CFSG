module

public import CFSG.ClassicalInvolution.Q3.Q3URStmt
public import CFSG.ClassicalInvolution.Phan.Phan3TFinal

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

theorem phan3Rec_proved : Phan3Rec :=
  fun hn _ _ _ _ hW hT => Phan.Q3G.phan3Rec_of_tripleBlocks hn hW hT

end CFSG.ClassicalInvolution.Q3.Q3W
