module

public import CFSG.GF2Type.SmithTypeE.E7.OmegaSix
public import CFSG.GF2Type.SmithTypeE.GH74Inputs
public import CFSG.GF2Type.Smith1980Orth.SixFinal
public import CFSG.GF2Type.Smith1980Orth.TimGH74
public import CFSG.GF2Type.Smith1980Orth.Ident
public import CFSG.GF2Type.SmithTypeE.E7.Assembly
public import CFSG.GF2Type.SmithTypeE.E7.Levi
public import CFSG.GF2Type.SmithTypeE.E7.Path

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GF2Type.SmithTypeE.E7

theorem partC_of_chain_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) (h33 : SmithE7E33)
    (h34Q : SmithE7E34Q) (h23 : SmithE7E23) (h24 : SmithE7E24) (hLine : SmithE7E24Line)
    (h25 : SmithE7E25) (h23f : SmithE7E23Four) (h261 : SmithE7E261) : PartC := by
  obtain ⟨hAS, hDW, hHolt, -⟩ := smithTypeEInputs_of_gh74 hgh
  have hOrth6 := GF2Type.Smith1980Orth.smith1980OrthogonalSix_of_timInputs
    (GF2Type.Smith1980Orth.timInputs_of_gh74 hgh) hHolt GF2Type.Smith1980Orth.identInput
  obtain ⟨h34a, h34b⟩ := smithE7E34_of h33 h34Q
  exact partC_of_smithE7Input_six hOrth6 (smithE7Input_of_threeFour (smithE7ThreeFourInput_of hAS
    hDW hHolt (smithE7LocalInput_of h34a h34b h23 h24 h25 h23f)
    (smithE7PathInput_of h34a h34b h23 h24 h25 h23f hLine (smithE7E421Three_of h34a h261))))

end CFSG.GF2Type.SmithTypeE
