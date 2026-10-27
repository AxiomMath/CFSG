module

public import Certificates.Data.Kernel.F2FixRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData

public section

namespace CFSG.KD.M13.r16957

open CFSG.KC.F2FixRank CFSG.Monster.B CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

@[expose] def code (p : Model.Pauli) : ℕ := p.2.1 + 4096 * p.2.2

@[expose] def col (j : ℕ) : ℕ := if j < 12 then code imgT13[j]! else code imgD13[j - 12]!

@[expose] def bcol (k : ℕ) : ℕ :=
  [12103432, 10722263, 15829478, 8876283, 10151181, 8759464, 689804, 13965328, 9002009, 32565,
    8932888, 6027607, 11647236, 8440288, 10822577, 5706848, 16361348, 2149454, 8710058, 976470,
    11631703, 4472020, 3478520, 8024867].getD k 0

theorem rank_ok : fixRankOK col bcol [] 24 = true := by decide +kernel

end CFSG.KD.M13.r16957

end
