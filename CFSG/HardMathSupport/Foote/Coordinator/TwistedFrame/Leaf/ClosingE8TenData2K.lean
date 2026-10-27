module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenDataK
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

@[expose] def e8tK_wLit : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 0, 0, -1, 0, 0, 2;
    1, 0, 0, 0, -1, 0, 0, 3;
    0, 0, 0, 1, -2, 0, 0, 4;
    0, 0, 1, 0, -2, 0, 0, 6;
    0, 0, 0, 0, -1, 0, 0, 5;
    0, 0, 0, 0, -1, 0, 1, 3;
    0, 0, 0, 0, -1, 1, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 1]

theorem e8tK_wordw : wordMat Tag.E8 TwClass.wordE8Ten = e8tK_wLit := by decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

end
