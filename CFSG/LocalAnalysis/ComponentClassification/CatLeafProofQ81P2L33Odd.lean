module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def OddClsRow (t : StatedLieTag) : Prop :=
  TwoNilpFor fun Y _ => ∃ n p f : ℕ, p ≠ 2 ∧ StatedClassicalModel Y t n p f

theorem twoNilpFor_odd_of_rows (hL : OddClsRow .PSL) (hU : OddClsRow .PSU)
    (hSp : OddClsRow .PSp) (hO : OddClsRow .POmegaOdd) (hP : OddClsRow .POmegaPlus)
    (hM : OddClsRow .POmegaMinus) :
    TwoNilpFor fun Y _ => ∃ t n p f, p ≠ 2 ∧ StatedClassicalModel Y t n p f := by
  intro Y _ _ hY
  obtain ⟨t, n, p, f, hp, h⟩ := hY
  cases t
  · exact hL Y ⟨n, p, f, hp, h⟩
  · exact hU Y ⟨n, p, f, hp, h⟩
  · exact hSp Y ⟨n, p, f, hp, h⟩
  · exact hO Y ⟨n, p, f, hp, h⟩
  · exact hP Y ⟨n, p, f, hp, h⟩
  · exact hM Y ⟨n, p, f, hp, h⟩
  all_goals exact h.2.elim

theorem oddClsRow_psl_of
    (h3 : TwoNilpFor fun Y _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ StatedClassicalModel Y .PSL n p f) :
    OddClsRow .PSL := by
  intro Y _ _ hY
  obtain ⟨n, p, f, hp, h⟩ := hY
  by_cases hn : 3 ≤ n
  · exact h3 Y ⟨n, p, f, hn, hp, h⟩
  · have hn2 : n = 2 := by
      obtain ⟨⟨-, -, hn2, -, -⟩, -⟩ := h
      omega
    subst hn2
    exact fun _ _ _ _ _ => Or.inl ⟨p, f, Or.inl ⟨by decide, h⟩⟩

end CFSG.ComponentClassification.HarrisLit.L33
