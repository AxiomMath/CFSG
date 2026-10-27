module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.GroupTheory.SteinbergBK

universe u

theorem odd_noncyclic_pgroup_rank_two {p : ℕ} [Fact p.Prime] (hodd : Odd p) {P : Type u}
    [Group P] [Finite P] (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) :
    ∃ B : Subgroup P, IsElementaryAbelian p B ∧ Nat.card B = p ^ 2 := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd even_two
  obtain ⟨B, -, hcard, helem⟩ := CFSG.lemma_4_5_a hp2 hnc
  exact ⟨B, helem, hcard⟩

end CFSG.GroupTheory.SteinbergBK
