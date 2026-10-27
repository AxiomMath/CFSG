
module


public import CFSG.Certificates.Kernel.SporSch.ThColsProved

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

theorem colK_sound {R : Nat → Nat} {x : Nat} (hR : ∀ i < 248, R i < 2 ^ 248) (hx : x < 2 ^ 248) :
    frApply (frTable (transposeRows (rowsV R))) (v4OfNat x) = v4OfNat (colK R x) :=
  colK_sound_proved hR hx

end CFSG.KS.SporSch

end
