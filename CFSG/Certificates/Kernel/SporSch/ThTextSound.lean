module

public import Certificates.Data.Kernel.SporSch.ThText
public import CFSG.Sporadic.ThSchreier.Text
import CFSG.Certificates.Kernel.SporSch.ThTextProved

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.ThSchreier

theorem thScan_sound {hex : Bool} {B v : Nat} {cs : List Char}
    (h : thScanK hex B v cs % 2 = 0) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = thScanK hex B v cs / 4 ∧ (∀ n ∈ L, n < B) ∧
      (v ∈ L ↔ thScanK hex B v cs / 2 % 2 = 1) :=
  thScan_sound_proved h

theorem thBind_sound {hex : Bool} {R : Nat → Nat} {cs : List Char}
    (h : thBindK hex R cs % 2 = 0) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = thBindK hex R cs / 2 ∧ ∀ t < L.length, L.getD t 0 = R t :=
  thBind_sound_proved h

end CFSG.KS.SporSch

end
