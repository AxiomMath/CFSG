module

public import CFSG.ClassicalInvolution.Q3.TA3SOLA0
public import CFSG.ClassicalInvolution.Q3.TA3SOLL3U3
public import CFSG.ClassicalInvolution.Q3.TA3SOLSp4
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4
public import CFSG.ClassicalInvolution.Q3.TA3SOLL5U5

public section

namespace CFSG.ClassicalInvolution.Q3.TA3


theorem smallOddLieTightMemberS_holds : SmallOddLieTightMemberS :=
  smallOddLieTightMemberS_of_packages noDatumL3U3_holds noDatumSp4_holds noDatumL4U4_holds
    noDatumL5U5_holds

end CFSG.ClassicalInvolution.Q3.TA3
