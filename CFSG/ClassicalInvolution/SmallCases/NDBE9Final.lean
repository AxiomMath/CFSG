module

public import CFSG.ClassicalInvolution.SmallCases.NDBE9Model
public import CFSG.ClassicalInvolution.SmallCases.NDBE8Final

public section

namespace CFSG.ClassicalInvolution.NDB

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem exoticFrameSpin_proved : ExoticFrameSpin p f :=
  exoticFrameSpin_of p f (spinOuterKleinAlpha_proved p)

end CFSG.ClassicalInvolution.NDB
