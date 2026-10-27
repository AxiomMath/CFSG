module

public import CFSG.GH74.GLS.SP.Local.SPLR2a
public import CFSG.GH74.GLS.SP.Local.SPLR2b
public import CFSG.GH74.GLS.SP.Local.SPLR2c

public section

namespace CFSG.GH74.GLS.SP.Local

theorem splLeafR2_of_inputs (hNM : NatModStmt) (h33 : SPLInL33) (h34 : SPLInL34) (hC2 : SPLInC2) :
    SPLLeafR2 := by
  intro G _ _ hG D hs h1 hc ho h3 hA
  have hCX := hC2 G hG D hs h1 hc h3
  have hD1 := h33 G hG D hs h1 hc ho h3 hA
  have hD2 := h34 G hG D hs h1 hc ho h3 hA
  have hRA := r2A_of_inputs D hs h1 hc h3 hCX
  have hRB := r2B_of_inputs D hs h1 h3 hA hRA hD1 hD2
  exact r2C_of_inputs hNM D hs h1 hc ho h3 hA hRA hRB hD1 hD2 hCX

end CFSG.GH74.GLS.SP.Local
