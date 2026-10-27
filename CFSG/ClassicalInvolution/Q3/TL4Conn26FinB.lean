module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Fin
public import CFSG.ClassicalInvolution.Q3.TL4Conn26S4B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

section Cit3

variable {r n : ℕ}

theorem tightConnLeafR'_of_residuals₇ (hD : TightS26DichR r n) (h26_13 : TightC26_13R r n)
    (h5 : TightSec5CliqueR r n) (hB : TightBenderEndR) (hE4g : TightE4SecGenR r n)
    (hLC : TightLambdaCommR r n) (hTri : TightSecTriangleR r n) (hT4 : Thm4RBelow r n)
    (hH : TightHyp51TriR r n) (hF : TightAlphaFrameR r n) (hNR : TightSecNoRootR r n) :
    TightConnLeafR' r n :=
  tightConnLeafR'_of_residuals₆ (tightC26_2R_of hD hLC) h26_13 h5 hB hE4g hLC hTri hT4 hH hF hNR

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
