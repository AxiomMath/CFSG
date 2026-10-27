module

public import CFSG.ClassicalInvolution.Asc77.AscBSD4
public import CFSG.ClassicalInvolution.Asc77.AscBSD11

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC

variable {p f : ℕ} [Fact p.Prime]


theorem BootShapeResidualsNarrow.toResiduals (h : BootShapeResidualsNarrow p f) :
    BootShapeResiduals p f where
  noAllA1 := h.noAllA1
  noG2D4 := BSD.bootNoG2D4 h.noG2Twin h.noG2D4Single
  noM3Twin := BSD.bootNoM3Twin
  noSmallSingle := h.noSmallSingle
  noManyTwins := BSD.bootNoManyTwins h.noD4Twins
  twinsCommute := h.twinsCommute

theorem bootShapeCover_of_narrow (h : BootShapeResidualsNarrow p f) : BootShapeCover p f :=
  bootShapeCover_of_residuals h.toResiduals

end CFSG.ClassicalInvolution.Asc77.BSC
