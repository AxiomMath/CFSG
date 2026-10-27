module

public import CFSG.ClassicalInvolution.Q3.TL3T23
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


@[expose] def PackIH (r : ℕ) (n : ℕ) : Prop := CIT3Below n ∧ TL4.TightBelowRPlus r n

theorem thmD2Step_of_leaves {r : ℕ} (h8 : DLeafZ8 r (PackIH r)) (hC : DLeafC r (PackIH r))
    (hE4 : DLeafE4 r (PackIH r)) (hstar : DLeafStar r (PackIH r))
    (hend : DLeafEnd r (PackIH r)) (n : ℕ) :
    CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) := fun hA hP =>
  thmDAbsBelow_succ (dLeafZ_of h8) hC (dLeafCls_holds r) hE4 hstar hend ⟨hA, hP⟩ hP.thmD.d2

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
