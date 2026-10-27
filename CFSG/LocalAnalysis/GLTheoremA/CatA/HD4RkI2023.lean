module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem prime_ne_three_of_card_eq {q q' : TauCeti.PrimePower} (hq : q.p = 2)
    (hcard : q'.card = q.card) : q'.p ≠ 3 := by
  intro h3
  have h1 : 3 ∣ q'.card := by
    rw [TauCeti.PrimePower.card_def, h3]
    exact dvd_pow_self 3 q'.exponent_pos.ne'
  rw [hcard, TauCeti.PrimePower.card_def, hq] at h1
  have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h1
  norm_num at h2

section Rank


theorem I2023FactD4RankTwo_holds : I2023FactD4RankTwo := by
  intro S _ _ q hq hcat E hE
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie j =>
    obtain ⟨d, hd⟩ := j
    cases d with
    | trialityD4 q' =>
      have hcard : q'.card = q.card := hi
      have hR := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q' hd
        (prime_ne_three_of_card_eq hq hcard)
      have h9 := CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm hR E hE
      exact h9.trans (by norm_num)
    | _ => exact hi.elim
  | _ => exact hi.elim

end Rank

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
