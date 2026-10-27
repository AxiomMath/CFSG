module

public import Certificates.Data.Kernel.F2FixRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData

public section

namespace CFSG.KD.E11.r16953

open CFSG.KC.F2FixRank CFSG.Monster.B CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

@[expose] def code (p : Model.Pauli) : ℕ := p.2.1 + 4096 * p.2.2

@[expose] def col (j : ℕ) : ℕ := if j < 12 then code imgT11[j]! else code imgD11[j - 12]!

@[expose] def bcol (k : ℕ) : ℕ :=
  [4741304, 104815, 52394, 4768768, 4234262, 4298825, 4767449, 380498, 4282277, 4305457, 549498,
    392395, 5006034, 646813, 794316, 125403, 551222, 848054, 585035, 0, 0, 0, 0, 861116].getD k 0

@[expose] def fs : List ℕ := [17, 20, 21, 23]

theorem rank_ok : fixRankOK col bcol fs 24 = true := by decide +kernel

end CFSG.KD.E11.r16953

end
