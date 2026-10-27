module

public import CFSG.ClassicalInvolution.Q3.Q3DStand
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Uniform.U4Class
public import CFSG.ClassicalInvolution.Uniform.UBranchProof
public import CFSG.ClassicalInvolution.Uniform.U4Bstar
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.ClassicalInvolution.Uniform.U3Thm7
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Three2
public import CFSG.ClassicalInvolution.Uniform.U8Final
public import CFSG.ClassicalInvolution.Uniform.U9G2
public import CFSG.ClassicalInvolution.ModelFacts.TG3Final
public import CFSG.ClassicalInvolution.Uniform.U9NoExc
public import CFSG.ClassicalInvolution.Asc77.AscFusionR11
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6
public import CFSG.ClassicalInvolution.Uniform.U4Resid

public section

namespace CFSG.ClassicalInvolution.Q3.Disc3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform

theorem twinNoExc3_proved : ModelFacts.TG3.TwinNoExc3 :=
  noTwinExc3

theorem twinGen3_proved : TwinGen3 :=
  ModelFacts.TG3.twinGen3_of twinNoExc3_proved

end CFSG.ClassicalInvolution.Q3.Disc3
