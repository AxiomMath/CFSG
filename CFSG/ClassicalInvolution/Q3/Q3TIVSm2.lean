module

public import CFSG.ClassicalInvolution.Q3.Q3TIVDefs
public import CFSG.ClassicalInvolution.Q3.Q3TCDict
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Q3.Q3TY32
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TP



theorem yData3S_of_yData3 {tY : StatedLieTag} {nY : ℕ} (h : YData3 tY nY) : YData3S tY nY :=
  ⟨h.sc, h.perfK, h.pow3, h.central, h.cop⟩

theorem exists_noncommuting3 {tY : StatedLieTag} {nY : ℕ} (hfund : Generic.IsFundTag tY)
    (hadm : StatedLieAdmissible tY nY 3 1) (hnA1 : ¬ (tY = .PSL ∧ nY = 2)) :
    ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      ∃ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
        S ≠ R ∧ ¬ Commutes S R :=
  fun _ hR => Exotic.exists_fund_not_commuting (p := 3) (e := 1) hfund hadm hnA1 hR

theorem twinRowFacts3_plus {n : ℕ} (hn : 4 ≤ n) : TwinRowFacts3 .POmegaPlus n := by
  have hadm : StatedLieAdmissible .POmegaPlus n 3 1 := ⟨Nat.prime_three, Nat.one_pos, hn⟩
  exact ⟨yData3S_of_yData3 (Q3W.yData3_plus hn hadm),
    RouteD.nonempty_fund_plus (p := 3) (f := 1) hn,
    exists_noncommuting3 (tY := .POmegaPlus) (nY := n) trivial hadm
      fun h => absurd h.1 (by decide)⟩

theorem twinRowFacts3_sl4 : TwinRowFacts3 .PSL 4 := by
  have hadm : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide, by decide⟩
  exact ⟨yData3S_of_yData3 (Q3TC.yData3_sl4 hadm), ⟨_, Q3TC.rankOne_mem_fund_sl4_three hadm 0⟩,
    exists_noncommuting3 (tY := .PSL) (nY := 4) trivial hadm (by decide)⟩

theorem twinRowFacts3_odd {n : ℕ} (hn : 3 ≤ n) : TwinRowFacts3 .POmegaOdd n := by
  have hadm : StatedLieAdmissible .POmegaOdd n 3 1 :=
    ⟨Nat.prime_three, Nat.one_pos, hn, by norm_num⟩
  exact ⟨yData3S_of_yData3 (Q3W.yData3_odd hn hadm),
    RouteD.nonempty_fund_odd (p := 3) (f := 1) hn,
    exists_noncommuting3 (tY := .POmegaOdd) (nY := n) trivial hadm
      fun h => absurd h.1 (by decide)⟩

theorem twinRowFacts3_sp2 : TwinRowFacts3 .PSp 2 := by
  obtain ⟨R, hR, -⟩ := Q3TP.exists_noncommuting_fund_psp2
  exact ⟨Q3TP.yData3S_psp2, ⟨R, hR⟩,
    exists_noncommuting3 (tY := .PSp) (nY := 2) trivial Q3Z.statedLieAdmissible_psp2
      (by decide)⟩

theorem twinRowFacts3_minus {n : ℕ} (hn : 4 ≤ n) : TwinRowFacts3 .POmegaMinus n := by
  have hadm : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, Nat.one_pos, hn⟩
  exact ⟨yData3S_of_yData3 (Q3W.yData3_minus hn hadm),
    RouteD.nonempty_fund_minus (p := 3) (f := 1) hn,
    exists_noncommuting3 (tY := .POmegaMinus) (nY := n) trivial hadm
      fun h => absurd h.1 (by decide)⟩

theorem twinRowFacts3_su4 : TwinRowFacts3 .PSU 4 := by
  have hadm : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide⟩
  obtain ⟨R, hR, -⟩ := Q3TY.exists_noncommuting_fund_psu4
  exact ⟨Q3TY.yData3S_psu4, ⟨R, hR⟩,
    exists_noncommuting3 (tY := .PSU) (nY := 4) trivial hadm (by decide)⟩

theorem twinRowFacts3_of_row {t : StatedLieTag} {n : ℕ}
    (hrow : CFSG.ClassicalInvolution.RouteD.TwinY.TwinRow t n) : TwinRowFacts3 t n := by
  rcases hrow with ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ |
    ⟨-, rfl, rfl⟩
  · exact twinRowFacts3_plus hn
  · exact twinRowFacts3_sl4
  · exact twinRowFacts3_odd hn
  · exact twinRowFacts3_sp2
  · exact twinRowFacts3_minus hn
  · exact twinRowFacts3_su4

end CFSG.ClassicalInvolution.Q3.Q3TIV
