module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporM

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

theorem hinFor_sporadicRep_of_rows
    (hHS : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .HS)
    (hHe : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .He)
    (hON : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .ONan)
    (hSuz : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Suz) :
    HinFor fun Y _ => Blueprint.NativeSporadic.SporadicRep Y := by
  intro Y _ _ _ ⟨s, hs⟩
  cases s
  case M11 => exact hinFor_spor_M11 Y hs
  case M12 => exact hinFor_spor_M12 Y hs
  case M22 => exact hinFor_spor_M22 Y hs
  case M23 => exact hinFor_spor_M23 Y hs
  case M24 => exact hinFor_spor_M24 Y hs
  case J1 => exact hinFor_spor_J1 Y hs
  case J2 => exact hinFor_spor_J2 Y hs
  case J3 => exact hinFor_spor_J3 Y hs
  case J4 => exact hinFor_spor_J4 Y hs
  case HS => exact hHS Y hs
  case McL => exact hinFor_spor_McL Y hs
  case He => exact hHe Y hs
  case Ru => exact hinFor_spor_Ru Y hs
  case Suz => exact hSuz Y hs
  case ONan => exact hON Y hs
  case Co1 => exact hinFor_spor_Co1 Y hs
  case Co2 => exact hinFor_spor_Co2 Y hs
  case Co3 => exact hinFor_spor_Co3 Y hs
  case Fi22 => exact hinFor_spor_Fi22 Y hs
  case Fi23 => exact hinFor_spor_Fi23 Y hs
  case Fi24Prime => exact hinFor_spor_Fi24Prime Y hs
  case HN => exact hinFor_spor_HN Y hs
  case Ly => exact hinFor_spor_Ly Y hs
  case Th => exact hinFor_spor_Th Y hs
  case B => exact hinFor_spor_B Y hs
  case M => exact hinFor_spor_M Y hs

end CFSG.ComponentClassification.HarrisLit.Hin
