module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU

public section

namespace CFSG.ClassicalInvolution.Asc77

section Call

variable {p f : ℕ} [Fact p.Prime]

theorem twinFrameHyp51t_proved (hres : TwinSmallInner p) : TwinFrameHyp51t p f :=
  twinFrameHyp51t_of hres g2d4VertexExcl_proved

theorem twinFrameHyp51u_proved (hres : TwinSmallOuter p) : TwinFrameHyp51u p f :=
  twinFrameHyp51u_of hres g2d4VertexExcl_proved

theorem twinFrameHyp51_proved (hin : TwinSmallInner p) (hout : TwinSmallOuter p) :
    TwinFrameHyp51 p f :=
  twinFrameHyp51_of hin hout g2d4VertexExcl_proved

theorem c21_3_proved (hin : TwinSmallInner p) (hout : TwinSmallOuter p) : C21_3 p f :=
  c21_3_of_residuals hin hout g2d4VertexExcl_proved

end Call

end CFSG.ClassicalInvolution.Asc77
