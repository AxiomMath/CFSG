module

public import CFSG.GF2Type.SmithTypeE.E7.PartC
public import CFSG.GF2Type.SmithTypeE.E8.Chain
public import CFSG.GF2Type.SmithTypeE.E8.ModCert
public import CFSG.GF2Type.SmithTypeE.E8.E23FourCert
public import CFSG.GF2Type.SmithTypeE.E8.E261Inputs
public import CFSG.GF2Type.SmithTypeE.E8.CompatOf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

theorem partD_of_gh74_e33 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models)
    (hC : E8.SmithE8Compat) (h33 : E8.SmithE8E33) : PartD := by
  obtain ⟨hAS, hDW, hHolt, -⟩ := smithTypeEInputs_of_gh74 hgh
  have hModel := E8.smithE8Model_of_compat hC
  have hMod := E8.smithE8Module_of_model hModel
  have h34Q := E8.smithE8E34Q_of_module hMod
  obtain ⟨h34a, h34b⟩ := E8.smithE8E34_of h33 h34Q
  have h24 := E8.smithE8E24_of_module hMod
  exact partD_of_chain hAS hDW hHolt (smithE7Input_of_gh74_only hgh) h33 h34Q
    (E8.smithE8E23_of_module hMod) h24 (E8.smithE8E24Line_of_module hMod)
    (E8.smithE8E25_of_module hMod) (E8.smithE8E23Four_of_model hModel h33 h34a h34b h24)
    (E8.smithE8E261_of_inputs hC h33 E8.e8ModelFacts E8.e23FourFacts8)

theorem partD_of_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) : PartD := by
  obtain ⟨hAS, -, -, I⟩ := smithTypeEInputs_of_gh74 hgh
  exact partD_of_gh74_e33 hgh (E8.smithE8Compat_of I hAS) (E8.smithE8E33_of I hAS)

end CFSG.GF2Type.SmithTypeE
