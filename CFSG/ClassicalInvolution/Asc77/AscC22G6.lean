module

public import CFSG.ClassicalInvolution.Asc77.AscC22G5
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace C22G

variable {p f : ℕ} [Fact p.Prime]


theorem c22_dstarConn_of_layerStar_proved (h : C22_layerStar p f) : C22_dstarConn p f :=
  c22_dstarConn_of_layerStar (thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all) h

theorem c22_8Gen_of_layerStar (h : C22_layerStar p f) : C22_8Gen p f :=
  c22_8Gen_of_dstarConn p f (c22_dstarConn_of_layerStar_proved h)

end C22G

end CFSG.ClassicalInvolution.Asc77
