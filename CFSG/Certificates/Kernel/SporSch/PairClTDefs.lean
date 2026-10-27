module

public import Certificates.Data.Kernel.SporSch.PairClT
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

@[expose] def TabsT (n w kS nb BP NR NL : Nat) (PS PSI LR Ts LT PT QT : Nat → Nat)
    (NT BT NQ BQ : Nat) : Prop :=
  n ≤ 64 * NR ∧ n ≤ 64 * NL ∧ (kS + kS) * n ≤ NT * BT ∧ n ≤ NQ * BQ ∧
    (∀ i < nb, Nat.beq (Ts i) (stepsAt n w PS kS BP i) = true) ∧
    (∀ s < NT, allBlk (Nat.mul s BT) (ltOKT n w kS NR PS PSI LT) BT = true) ∧
    (∀ i < nb, ∀ s < NQ, allBlk (Nat.mul s BQ) (ptOKT n w NL LR Ts PT i) BQ = true) ∧
    ∀ i < nb, ∀ s < NQ, allBlk (Nat.mul s BQ) (qtOKT n w NL LR QT i) BQ = true

@[expose] def ClosNFT (n w kS nb NR NL : Nat) (LR LT PT QT : Nat → Nat) (bs : List Nat)
    (kg : Nat) (GL : Nat → Nat) (RP : List Nat) (c cap nS R H nB B : Nat)
    (X W K C SO SOI : Nat → Nat) : Prop :=
  0 < c ∧ c ≤ cap ∧ c ≤ nS * R * H ∧ c ≤ nB * R * B ∧ c < 2 ^ 20 ∧ kg < 256 ∧ nb < 8 ∧
    (∀ l < kg, GL l < kS + kS) ∧ canonL n w RP = true ∧ ltL n bs = true ∧
    startNFT n w kS NR NL LT PT QT nb (wordKey n w bs RP) (X 0) = true ∧
    Nat.beq (K 0) (wordKey n w bs RP) = true ∧
    (∀ g < nB, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B)
      (recOKT n w NR NL LT PT nb bs (fun t => rcnt (LR t)) X K c) B = true) ∧
    (∀ g < nB, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B)
      (keySortAt [(c, K)] SO SOI c) B = true) ∧
    C 0 = 1 ∧ C (Nat.mul nS R) = c ∧
    ∀ g < nS, ∀ r < R, Nat.beq (runNFT n w kS NR NL LT PT QT nb bs GL X W K kg c H
      (Nat.mul (Nat.add (Nat.mul g R) r) H) (C (Nat.add (Nat.mul g R) r)))
      (C (Nat.succ (Nat.add (Nat.mul g R) r))) = true

end CFSG.KS.SporSch

end
