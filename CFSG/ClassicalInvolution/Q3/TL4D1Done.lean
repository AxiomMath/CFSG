module

public import CFSG.ClassicalInvolution.Q3.TL4D1Dis
public import CFSG.ClassicalInvolution.Q3.TL4D1MAll

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

theorem d1Core3 (n : ℕ) : D1Core3 n := d1Core3_of_facts d1Facts n

end CFSG.ClassicalInvolution.Q3.TL4
