module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Delta
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Isolation
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.HNLike
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinus
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Orbit67

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7
  CFSG.LargeExtraspecial.S8 Module
open CFSG.Assembly (InCatalog)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem widthFourOmegaMinusCentral_of_inputs
    (hS : SchreierFor InCatalog) (hF : FilterW4MinusInCatalog) :
    WidthFourOmegaMinusCentral := by
  intro G _ _ _ _ _ hK S hw hno hirr g H C hsw t ht ht1 hVQ hΩ h4 hP x hx
  have hCE : CentralExtInput.{0} := S4.centralExtInput
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  have hSC : ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ = t := by
    rcases delta_dichotomy hCE hw H hNo C ht ht1 hVQ hΩ h4 hP with h1 |
        ⟨hΔ4, θ, hθR, hθ3, hθN, hθC, hΔmul, hΔK⟩
    · exact CaseIClosure.strongClosed_of_normalizer H C ht h1
    · exact (false_of_delta_four hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hS hK
        (CFSG.LargeExtraspecial.S14.irr_of_not_isReducible hirr) hsw hF hΔ4 hθR hθ3 hθN hθC
        hΔmul hΔK fun y hy hyN =>
          conj_mem_Lbar_of_mem_normalizer_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP hy hyN).elim
  exact comm_mem_Obar_w4 hw H hNo C ht ht1 hVQ hΩ h4
    (orbit67_w4 hCE hw H hNo C ht ht1 hVQ hΩ h4 hP) hSC hx

theorem widthFourOmegaMinusCentral_holds :
    WidthFourOmegaMinusCentral :=
  widthFourOmegaMinusCentral_of_inputs CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
    (filterW4MinusInCatalog_of_bridge CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge)

end CFSG.GF2Type.Smith1979.W4MinusC
