module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

structure UniqWit where
  J : ℕ
  y : ℕ → ℕ
  cl : ℕ → ℕ
  kind : ℕ → ℕ
  conj : ℕ → List (ℕ × ℕ)
  dl : ℕ → List ℕ
  c0 : List ℕ

@[expose] def clsOKW (N : ℕ) (commB : ℕ → ℕ → Bool) (conjB : ℕ → ℕ → ℕ → Bool) (W : UniqWit)
    (j : ℕ) : Bool :=
  decide (W.y j < N) &&
    ((W.conj j).all fun p => decide (p.1 < N) && decide (p.2 < N) && conjB p.1 (W.y j) p.2) &&
    (if W.kind j = 0 then (W.conj j).any fun p => !commB (W.y j) p.2
    else if W.kind j = 1 then
      ((List.range N).all fun i =>
          ((W.conj j).all fun p => commB i p.2) == (W.dl j).contains i) &&
        ((W.dl j).all fun a => decide (a < N)) &&
        ((W.dl j).all fun a => (W.dl j).all fun b => commB a b) &&
        decide ((W.dl j).Pairwise (· < ·)) &&
        ((W.dl j).length != 64 || W.dl j == W.c0)
    else true)

@[expose] def uniqCheckW (N : ℕ) (commB : ℕ → ℕ → Bool) (conjB : ℕ → ℕ → ℕ → Bool)
    (invB : ℕ → Bool) (W : UniqWit) : Bool :=
  ((List.range W.J).all (clsOKW N commB conjB W)) &&
    decide (((List.range N).filter fun i => invB i && decide (2 ≤ W.kind (W.cl i))).length < 63)

@[expose] def clsPartW (N : ℕ) (commB : ℕ → ℕ → Bool) (conjB : ℕ → ℕ → ℕ → Bool) (W : UniqWit)
    (j : ℕ) : Bool :=
  decide (W.y j < N) &&
    ((W.conj j).all fun p => decide (p.1 < N) && decide (p.2 < N) && conjB p.1 (W.y j) p.2) &&
    (if W.kind j = 0 then (W.conj j).any fun p => !commB (W.y j) p.2
    else if W.kind j = 1 then
      ((W.dl j).all fun a => decide (a < N)) && decide ((W.dl j).length ≤ 128) &&
        decide ((W.dl j).Pairwise (· < ·)) &&
        ((W.dl j).length != 64 || W.dl j == W.c0)
    else true)

@[expose] def dRowW (commB : ℕ → ℕ → Bool) (W : UniqWit) (j i : ℕ) : Bool :=
  !(decide (W.kind j = 1)) ||
    (((W.conj j).all fun p => commB i p.2) == (W.dl j).contains i)

@[expose] def dPairW (commB : ℕ → ℕ → Bool) (W : UniqWit) (j t : ℕ) : Bool :=
  !(decide (W.kind j = 1)) || !(decide (t < (W.dl j).length)) ||
    (W.dl j).all (commB ((W.dl j).getD t 0))

end CFSG.EvenSmallLie.OmegaEight.SplitC
