module

public import Certificates.Data.Kernel.SporSch.PairCl
public import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

@[expose] def ClosNFOK (n w _kS nb _BP : Nat) (_PS _PSI LR TR TRI : Nat → Nat) (bs : List Nat)
    (kg : Nat) (G GI : Nat → Nat) (RP : List Nat) (c cap nS R H nB B : Nat) (X W C : Nat → Nat) :
    Prop :=
  0 < c ∧ c ≤ cap ∧ c ≤ nS * R * H ∧ c ≤ nB * R * B ∧ c < 2 ^ 20 ∧ kg < 256 ∧ nb < 8 ∧
    (∀ l < kg, permOK n w (mask w) (n * w) (G l) (GI l) = true) ∧
    canonL n w RP = true ∧ ltL n bs = true ∧
    startNF n w LR TRI nb bs RP (X 0) = true ∧
    Nat.beq (nfKey n w LR TR nb bs (nfX nb (X 0))) (wordKey n w bs RP) = true ∧
    (∀ g < nB, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) (nfOKAt n w LR nb X c) B = true) ∧
    C 0 = 1 ∧ C (Nat.mul nS R) = c ∧
    ∀ g < nS, ∀ r < R, Nat.beq (runNF n w LR TR TRI nb bs G GI X W kg c H
      (Nat.mul (Nat.add (Nat.mul g R) r) H) (C (Nat.add (Nat.mul g R) r)))
      (C (Nat.succ (Nat.add (Nat.mul g R) r))) = true

end CFSG.KS.SporSch

end
