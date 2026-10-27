module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowSp4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowSp6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowG2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowTitsThree
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowRee8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem kd1912TwoRows3_holds :
    KD1912TwoRows3 := by
  refine kd1912TwoLieAt_of_facts Nat.prime_three (by norm_num) ?_
  intro S _ _ hS hnc d hd hP e
  obtain ⟨e⟩ := e
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | B n q =>
    rcases n with _ | _ | _ | _ | n
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · have hq : q.card = 8 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_B2_eight q hv hq e)
    · have hq : q.card = 2 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_B3_two q hv hq e)
    · simp [LieRows3] at hP
  | D n q =>
    rcases n with _ | _ | _ | _ | _ | n
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · have hq : q.card = 2 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_D4_two q hv hq e)
    · simp [LieRows3] at hP
  | G2 q =>
    have hq : q.card = 8 := by
      simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
    exact Or.inl (oddCoreFact_three_of_G2_eight hq hv e)
  | twistedA n q =>
    rcases n with _ | _ | _ | _ | _ | _ | n
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · simp [LieRows3] at hP
    · have hq : q.card = 8 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_twistedA3_eight q hq hv e)
    · have hq : q.card = 2 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_twistedA4_two q hv hq e)
    · have hq : q.card = 2 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
      exact Or.inl (oddCoreFact_three_of_twistedA5_two hv hq e)
    · simp [LieRows3] at hP
  | trialityD4 q =>
    have hq : q.card = 2 := by
      simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd.2
    exact Or.inl (oddCoreFact_three_of_trialityD4_two hq hv e)
  | tits => exact Or.inl (oddCoreFact_three_of_tits hv e)
  | reeF4 k =>
    have hk : k = 1 := by
      have h' : (3 = 3 ∧ k = 1) ∨ (3 = 5 ∧ k = 2) := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
      rcases h' with ⟨-, hk⟩ | ⟨h, -⟩
      · exact hk
      · exact absurd h (by norm_num)
    subst hk
    exact Or.inl (oddCoreFact_three_of_reeF4_one hv e)
  | _ => simp [LieRows3] at hP

end CFSG.LocalAnalysis.GLTheoremA.KD1912
