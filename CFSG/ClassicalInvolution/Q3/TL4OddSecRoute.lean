module

public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddSecAsm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem tightOddLeafR3_of_E3 {n : ℕ} (hα : TightAlphaLeafR 3 n) (hconn : TightConnLeafR' 3 n)
    (hsep : TightSepLeafRα 3 n) (hE3 : TightE3LeafR' 3 n) : TightOddLeafR 3 n :=
  tightOddLeafR_of_maxSec hα hconn hsep (tightMaxSecR_of_parts hα hE3)

theorem tightOddLeaf_of_E3 {n : ℕ} (hα : TightAlphaLeafR 3 n) (hconn : TightConnLeafR' 3 n)
    (hsep : TightSepLeafRα 3 n) (hE3 : TightE3LeafR' 3 n) : TightOddLeaf n :=
  tightOddLeaf_of_R (tightOddLeafR3_of_E3 hα hconn hsep hE3)

end CFSG.ClassicalInvolution.Q3.TL4
