module

public import CFSG.GroupTheory.LinearPGroup.StatedClassical
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA5

public section

namespace CFSG.SectionRank.QTK

theorem oddCharList_sectionalTwoRankLE_or_G2
    (hGL : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] [Finite K],
      (2 : K) ≠ 0 → CFSG.GH74.SectionalTwoRankLE (GL ι K) (2 * Fintype.card ι - 1))
    {S : Type} [Group S] [Finite S] (hB : OddCharList S) :
    CFSG.GH74.SectionalTwoRankLE S 7 ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .G2 p 1 := by
  rw [OddCharList] at hB
  obtain ⟨p, hpprime, hp2, hcases⟩ := hB
  rcases hcases with hPSL2 | hPSL3 | hPSp | hG2 | hPSL4 | hPSU4
  · obtain ⟨f, -, hmodel⟩ := hPSL2
    refine Or.inl ?_
    exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hmodel).1
      rfl).mono (by norm_num)
  · obtain ⟨f, -, hmodel⟩ := hPSL3
    rcases hmodel with hmodel | hmodel
    · refine Or.inl ?_
      exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hmodel).1
        rfl).mono (by norm_num)
    · refine Or.inl ?_
      exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hmodel).2.1
        rfl).mono (by norm_num)
  · refine Or.inl ?_
    exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hPSp).2.2
      rfl).mono (by norm_num)
  · exact Or.inr ⟨p, hpprime, hp2, hG2⟩
  · obtain ⟨-, hmodel⟩ := hPSL4
    refine Or.inl ?_
    exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hmodel).1
      rfl).mono (by norm_num)
  · obtain ⟨-, hmodel⟩ := hPSU4
    refine Or.inl ?_
    exact ((CFSG.LinearPGroup.sectionalTwoRankLE_of_statedClassicalModel hGL hp2 hmodel).2.1
      rfl).mono (by norm_num)

end CFSG.SectionRank.QTK
