module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] noncomputable def unpack (n w P : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => pg w (mask w) P i.val

@[expose] noncomputable def stepsAt (_n w : Nat) (PS : Nat → Nat) (kS BP i : Nat) : Nat :=
  stepTab kS (fixMaskK w (mask w) PS kS BP i)

@[expose] def Binds (n w : Nat) (PS : Nat → Nat) (kS nb BP : Nat) (S : Array (Array Nat))
    (base : Array Nat) : Prop :=
  0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536 ∧ S.size = kS ∧ (∀ j < kS, S[j]! = unpack n w (PS j)) ∧
    base.size = nb ∧ ∀ t < nb, base[t]! = pg w (mask w) BP t

@[expose] def LevelsOK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS nb BP : Nat) : Prop :=
  ∀ i < nb, levelK n w (mask w) (n * w) (mask (n * w)) (pidn n w) PS PSI TR TRI kS
    (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (LR i) = true

theorem forall_lt_succ {P : Nat → Prop} {k : Nat} (h : ∀ s < k, P s) (hk : P k) :
    ∀ s < k + 1, P s := by
  intro s hs
  rcases Nat.lt_or_ge s k with h1 | h1
  · exact h s h1
  · have : s = k := by omega
    subst this
    exact hk

theorem forall_lt_zero {P : Nat → Prop} : ∀ s < 0, P s := fun s hs => absurd hs (Nat.not_lt_zero s)

end CFSG.KS.Raw

end
