module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bN23b
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bN23c
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModA

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup Module CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.I21L

section CoresE25

theorem e25CoreStmt_holds : E25CoreStmt := by
  intro Q _ _ B' _ _ ρ x t z h H hab
  obtain ⟨hcard, V₁, V₂, h1, h2, h3, -, -, -, K⟩ := module_E25_abs H hab
  unfold E25Concl
  exact ⟨hcard, V₁, V₂, h1, h2, h3, K⟩

end CoresE25

section CoresA6


theorem a6CoreStmt_holds : A6CoreStmt := by
  intro Q _ _ B' _ _ ρ x t z h H hA6
  obtain ⟨V₁, V₂, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := module_A6_abs H hA6
  unfold A6Concl
  exact ⟨V₁, V₂, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem a6CentStmt_holds : A6CentStmt := by
  intro Q _ _ B' _ _ ρ x t z h H hA6
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcent, -⟩ := module_A6_abs H hA6
  exact hcent

theorem rankThreeStmt_holds : RankThreeStmt := by
  intro Q _ _ B' _ _ ρ x t z h s H hJ hs2 hs3
  exact rank_three_abs H hJ hs2 hs3

end CoresA6

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

section Steps

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem step23b_holds : Step23b := by
  intro G _ _ d z₀ h49 hd hz hinv h10 h14 h17 h19 h23a
  exact node23b_of_cores h49 hd hz hinv h10 h14 h17 h19 h23a a6CoreStmt_holds e25CoreStmt_holds

theorem step23c_holds : Step23c := by
  intro G _ _ d z₀ h49 hd hz h10 h14 h17s h17 h19 h20 h21 h23a h23b
  exact node23c_of_cores h49 hd hz h10 h14 h17s h17 h19 h20 h21 h23a h23b a6CentStmt_holds
    rankThreeStmt_holds

end Steps

end CFSG.LocalAnalysis.EvenBN.Tits.N
