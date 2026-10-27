
module

public import CFSG.Certificates.Kernel.SporSch.ThRowsDefs
import CFSG.Certificates.Kernel.SporSch.ThBindProved
import CFSG.Certificates.Kernel.SporSch.ThIdProved
import CFSG.Certificates.Kernel.SporSch.ThPayProved
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public import Certificates.Data.Kernel.SporSch.ThRows

@[expose] public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

theorem v4Bind_sound {a : Array V4} {R : Nat → Nat} (h : v4BindK a.toList R = true) :
    a = rowsV R :=
  v4Bind_sound_proved h

theorem mulId_sound {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248) (hY : ∀ i < 248, Y i < 2 ^ 248)
    (h : ∀ i < 248, vmT Y (X i) = 2 ^ i) :
    eqRows (mulRows (rowsV X) (rowsV Y)) (idRows ()) = true :=
  mulId_sound_proved hX hY h

theorem invRows_sound {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248) (h : ∀ i < 248, vmT Y (X i) = 2 ^ i) :
    invRows (rowsV X) = rowsV Y :=
  invRows_sound_proved hX hY h

theorem v4N_sound {x : V4} {n : Nat} (h : v4N x = n) : x = v4OfNat n :=
  v4N_sound_proved h

theorem canonN_sound {a b : Nat} (ha : a < 2 ^ 248) (hb : b < 2 ^ 248) :
    canon (v4OfNat a) (v4OfNat b) =
      ⟨v4OfNat (canonN a b % 2 ^ 256), v4OfNat (canonN a b / 2 ^ 256)⟩ :=
  canonN_sound_proved ha hb

theorem thPay_sound {R : Nat → Nat} {cs : List Char} (h : thPayK R cs = true) :
    rowsOf (String.ofList cs) = rowsV R :=
  thPay_sound_proved h

theorem mulRows_sound {X Y Z : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248) (h : ∀ i < 248, vmT Y (X i) = Z i) :
    mulRows (rowsV X) (rowsV Y) = rowsV Z :=
  mulRows_sound_proved hX hY h

theorem mulD120_sound {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248)
    (h : ∀ i < 248, vmT Y (X i) = if i < 120 then 2 ^ i else 0) :
    eqRows (mulRows (rowsV X) (rowsV Y)) rowsD120 = true :=
  mulD120_sound_proved hX hY h

theorem rowsAmI_sound {A : Nat → Nat} (hA : CFSG.Sporadic.Th.Max3.rowsA = rowsV A) (hb : ∀ i < 248, A i < 2 ^ 248) :
    rowsAmI = rowsV (fun i => Nat.xor (A i) (2 ^ i)) :=
  rowsAmI_sound_proved hA hb

end CFSG.KS.SporSch

end
