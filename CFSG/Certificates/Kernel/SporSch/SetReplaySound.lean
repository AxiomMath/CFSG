
module

public import Certificates.Data.Kernel.SporSch.SetReplay
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def SetReplayOK (n w s kg c bound nS H nB B R : Nat) (G GI X W SO SOI C : Nat → Nat)
    (start : List Nat) : Prop :=
  0 < n ∧ n + 1 < 2 ^ w ∧ n < 2 ^ 24 ∧ 0 < c ∧ c ≤ bound ∧ c ≤ nS * R * H ∧ c ≤ nB * R * B ∧
    c < 2 ^ 20 ∧ kg < 256 ∧
    (∀ k < kg, permOK n w (mask w) (n * w) (G k) (GI k) = true) ∧
    startK w s (X 0) start = true ∧
    (∀ g < nB, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) (eltAt n w s X c) B = true) ∧
    (∀ g < nB, ∀ r < R,
      allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) (sortAt w s X SO SOI c) B = true) ∧
    C 0 = 1 ∧ C (Nat.mul nS R) = c ∧
    ∀ g < nS, ∀ r < R, Nat.beq (runFrom w s G X W kg c bound H
      (Nat.mul (Nat.add (Nat.mul g R) r) H) (C (Nat.add (Nat.mul g R) r)))
      (C (Nat.succ (Nat.add (Nat.mul g R) r))) = true

end CFSG.KS.SporSch

end
