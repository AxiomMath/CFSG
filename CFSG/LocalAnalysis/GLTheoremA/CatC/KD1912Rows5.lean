module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowTits
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowRee32
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem kd1912TwoRows5_holds :
    KD1912TwoRows5 := by
  refine kd1912TwoLieAt_of_facts Nat.prime_five (by norm_num) ?_
  intro S _ _ hS hnc d hd hP e
  obtain ⟨e⟩ := e
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | tits => exact Or.inl (oddCoreFact_five_of_tits hv e)
  | reeF4 k =>
    have hk : k = 2 := by
      have h' : (5 = 3 ∧ k = 1) ∨ (5 = 5 ∧ k = 2) := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
      rcases h' with ⟨h, -⟩ | ⟨-, hk⟩
      · exact absurd h (by norm_num)
      · exact hk
    subst hk
    exact Or.inl (oddCoreFact_five_of_reeF4_two hv e)
  | suzuki k =>
    have hk : k = 2 := by
      have h' : 5 = 5 ∧ k = 2 := by
        simpa [CFSG.Yardstones.Md0ec50421ce4.k2Lie] using hd
      exact h'.2
    subst hk
    exact Or.inl (oddCoreFact_five_of_suzuki_two hv e)
  | _ => simp [LieRows5] at hP

end CFSG.LocalAnalysis.GLTheoremA.KD1912
