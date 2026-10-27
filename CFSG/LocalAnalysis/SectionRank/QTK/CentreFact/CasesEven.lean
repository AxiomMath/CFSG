module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Table
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small

public section

namespace CFSG.SectionRank.QTK.CentreFact

open CFSG.Open CFSG.Blueprint

theorem oddBound_of_even_list {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hT : TableRestricted S r) (hU : StatedClassicalModel S .PSU 5 2 2 → r ≠ 5)
    (h : ((∃ f : ℕ,
      (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel S .PSU 4 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) ∨
      StatedClassicalModel S .PSU 5 2 2 ∨ ReeTitsModel S .Tits 2 1)) : OddBound r S := by
  rcases h with ⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ |
    ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩ | hm | hm
  · exact absurd (tablePrime_psl_two hr hr2 (hT.classical hm)).2.1 (by norm_num)
  · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
    exact oddBound_of_psl_three hm hr hr3 hrq
  · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
    exact oddBound_of_psu_three hm hr hr3 hrq
  · exact absurd (hT.classical hm) not_tablePrime_psp
  · exact absurd (tablePrime_psu_four hr hr2 (hT.classical hm)).2.1 (by norm_num)
  · exact absurd (tablePrime_g2 (hT.chevalley (by decide) hm)).2.1 (by norm_num)
  · exact absurd (hT.chevalley (by decide) hm) not_tablePrime_trialityD4
  · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_twistedF4
  · exact absurd (hT.suzuki hm) not_tablePrime_twistedB2
  · exact absurd (tablePrime_psu_five_two_two hr (hT.classical hm)) (hU hm)
  · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_tits

theorem oddBound_of_even_high_rank_list {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime)
    (hT : TableRestricted S r)
    (h : (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1) ∨
      StatedClassicalModel S .PSp 3 2 1) : OddBound r S := by
  rcases h with ⟨n, -, hm⟩ | hm
  · exact absurd (hT.classical hm) (not_tablePrime_psl_two_one hr)
  · exact absurd (hT.classical hm) not_tablePrime_psp

end CFSG.SectionRank.QTK.CentreFact
