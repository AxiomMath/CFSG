module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Kernel
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Sylow3
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Count
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.ZStar
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Quot
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Exclusion
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

theorem widthFourOmegaPlusLayerFalse_holds :
    WidthFourOmegaPlusLayerFalse := by
  intro G _ _ _ hnab hchar hK S hw hno hirr g H C hsw t ht ht1 hVQ hΩ h4 hplus hq hfaith
  have hCE : CentralExtInput.{0} := S4.centralExtInput
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  obtain ⟨P, hPR, hP9⟩ := exists_le_Rbar_card_nine H C ht ht1 hVQ hΩ h4 hplus
  have hP3 := pow_three_of_mem hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
  have hPn := conj_mem_of_mem_Ct hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
  have hcomm4 := card_commutant_le hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
  have hK4 := card_dvd_four_of_fix hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 hcomm4
  have hKt := self_mem_of_fix_of_card_eq_four hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3 hcomm4
  have hKe := mul_self_of_fix hw H C ht ht1 hVQ h4
  have hKc := eq_t_of_fix_of_conj hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP3
    (fun _ => eq_id_of_commute_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9)
  have hKP := fix_of_commute H hPR
    (fun _ => pow_three_of_commute_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9)
  have hC32 := pow_thirtyTwo_mem H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hPn
  have hO2 := fix_of_normalized (S := S) (g := g) hP9 hKP hPn
  have hEtop := layer_eq_top hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hP3 hPn
  have hZ := exists_mem_layer_not_center H ht ht1 hPR hq hfaith hP3 hPn hKP hKc
  obtain ⟨A, τ, B, D⟩ := exists_layerData hw H C ht ht1 hPR hP9 hq hfaith hP3 hPn hK4 hKt hKe
    hKc hC32 hO2 hEtop hZ
  haveI : IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := hq.2
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hX := CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge _ hnonab
    (Case25.inCatalog_layer_quotient hK (Case25.M_ne_top_of_isSimpleGroup S) hq)
  exact false_of_layerData_catalog hX hnonab (card_layer_quot_dvd hw H ht1 h4)
    (card_layer_quot_le hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hK4 hP3 hPn) D

end CFSG.GF2Type.Smith1979.OmegaPlus
