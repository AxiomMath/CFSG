module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Exists
public import CFSG.ClassicalInvolution.SmallCases.NDBD4NDB
public import CFSG.ClassicalInvolution.SmallCases.NDBD4BSC
import CFSG.ClassicalInvolution.RouteD.ExoticD4GenMain

public section

namespace CFSG.ClassicalInvolution.NDB

variable {p f : ℕ} [Fact p.Prime]

theorem exoticD4FourFalse : ExoticD4FourFalse p f := fun _ _ _ _ hnab _ _ S hloc =>
  RouteD.Exotic.false_of_exoticD4Four hnab S hloc

theorem d4FiveCore_proved : D4FiveCore p f :=
  d4FiveCore_of_frame D4.frameExists_d4 exoticD4FourFalse

theorem noD4Twins_proved : NoD4Twins p f :=
  noD4Twins_of d4FiveCore_proved

theorem bootNoD4FiveComp_proved : Asc77.BSC.BootNoD4FiveComp p f :=
  bootNoD4FiveComp_of d4FiveCore_proved

end CFSG.ClassicalInvolution.NDB
