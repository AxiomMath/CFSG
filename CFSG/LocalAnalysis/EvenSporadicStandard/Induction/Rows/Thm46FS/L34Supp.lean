module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatSimple
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.ComponentClassification CFSG.ComponentClassification.GrSLit.L34Sec5S


theorem l34FixedCatalog_holds : L34FixedCatalog := by
  intro S _ _ hs hna hcat σ hσ P hPF hP hPne hL
  have : IsSimpleGroup S := hs
  refine cat_of_simple ?_ hna hcat ⟨hσ, hPF, hP, hPne⟩ hL
  intro s h1 h2 h3 h4 h5 h6 h7 h8
  cases s
  case M11 => exact HarrisLit.sporCompData_M11
  case M22 => exact HarrisLit.sporCompData_M22
  case M23 => exact HarrisLit.sporCompData_M23
  case M24 => exact HarrisLit.sporCompData_M24
  case J4 => exact HarrisLit.sporCompData_J4
  case McL => exact HarrisLit.sporCompData_McL
  case Ru => exact HarrisLit.sporCompData_Ru
  case Co1 => exact HarrisLit.sporCompData_Co1
  case Co2 => exact HarrisLit.sporCompData_Co2
  case Co3 => exact HarrisLit.sporCompData_Co3
  case Fi22 => exact HarrisLit.sporCompData_Fi22
  case Fi23 => exact HarrisLit.sporCompData_Fi23
  case Fi24Prime => exact HarrisLit.sporCompData_Fi24Prime
  case HN => exact HarrisLit.sporCompData_HN
  case Ly => exact HarrisLit.sporCompData_Ly
  case Th => exact HarrisLit.sporCompData_Th
  case B => exact HarrisLit.sporCompData_B
  case M => exact HarrisLit.sporCompData_M
  all_goals first
    | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4
    | exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 | exact absurd rfl h8

end CFSG.EvenSporadicStandard.Induction
