module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0X
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoL2B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoL3B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3Q
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12F
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4Sp6
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4O8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem exitTwoClassR_of {n : ℕ} (_hA : CIT3Below n) (hP : TightBelowRPlus 3 n) :
    ExitTwoClassR n :=
  ExitTwo.exitTwoClassR_of_rows hP.thm6 ExitTwo.socleTransitive_l2Sq
    ExitTwo.socleTransitive_l3Ge5 ExitTwo.socleTransitive_u3Ge5 ExitTwo.socleTransitive_u33
    ExitTwo.socleTransitive_m12 ExitTwo.socleTransitive_sp62 ExitTwo.socleTransitive_o8p2

end CFSG.ClassicalInvolution.Q3.TL4
