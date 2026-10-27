module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Table
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded

public section

namespace CFSG.SectionRank.QTK.CentreFact

open CFSG.Open CFSG.Blueprint

theorem oddBound_of_odd_list
    {S : Type} [Group S] [Finite S] {r p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hT : TableRestricted S r)
    (h : (∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 2 p f) ∨
      (∃ f : ℕ, (f = 1 ∨ f = 2) ∧
        (StatedClassicalModel S .PSL 3 p f ∨ StatedClassicalModel S .PSU 3 p f)) ∨
      StatedClassicalModel S .PSp 2 p 1 ∨ ChevalleyExceptionalModel S .G2 p 1 ∨
      ((∃ a : ℕ, p = 2 ^ a + 1) ∧ StatedClassicalModel S .PSL 4 p 1) ∨
      ((∃ b : ℕ, p + 1 = 2 ^ b) ∧ StatedClassicalModel S .PSU 4 p 1)) :
    OddBound r S := by
  rcases h with ⟨f, -, hm⟩ | ⟨f, -, hm | hm⟩ | hm | hm | ⟨-, hm⟩ | ⟨-, hm⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tablePrime_psl_two hr hr2 (hT.classical hm)
    exact oddBound_of_psl_two_nine hm hr hr2
  · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
    exact oddBound_of_psl_three hm hr hr3 hrq
  · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
    exact oddBound_of_psu_three hm hr hr3 hrq
  · exact absurd (hT.classical hm) not_tablePrime_psp
  · obtain ⟨rfl, rfl, -⟩ := tablePrime_g2 (hT.chevalley (by decide) hm)
    exact oddBound_three_of_g2_three hm
  · exact absurd (hT.classical hm) (not_tablePrime_psl_four hr hr2)
  · obtain ⟨rfl, rfl, -⟩ := tablePrime_psu_four hr hr2 (hT.classical hm)
    exact oddBound_three_of_u4_three hm

end CFSG.SectionRank.QTK.CentreFact
