module

public import CFSG.GF2Type.SmithTypeE.E6Assembly
public import CFSG.GF2Type.SmithTypeE.L6.Path
public import CFSG.GF2Type.SmithTypeE.L6.Levi
public import CFSG.GF2Type.SmithTypeE.L6Ident.E23a
public import CFSG.GF2Type.SmithTypeE.L6.E23FourCert
public import CFSG.GF2Type.SmithTypeE.L6Ident.Pair
public import CFSG.GF2Type.SmithTypeE.LMod.PairCent
public import CFSG.GF2Type.SmithTypeE.GH74Inputs
public import CFSG.Yardstones.M3aba7dc4b8a8.Assembly
public import CFSG.GF2Type.SmithTypeE.L6.CompatOf
public import CFSG.GF2Type.SmithTypeE.PartA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open
open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

theorem partB_of_gh74_only






 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) : PartB := by
  obtain ⟨hAS, hDW, hHolt, I⟩ := smithTypeEInputs_of_gh74 hgh
  have hC := L6.smithL6Compat_of I hAS
  have h33 := L6.smithL6E33_of I hAS
  have hMF := L6.modelFacts
  have hF := L6.e23FourFacts
  have hModel := L6.smithL6Model_of_compat hC
  have hModule := L6.smithL6Module_of_model hModel
  obtain ⟨h34a, h34b⟩ := L6.smithL6E34_of h33 (L6.smithL6E34Q_of hMF hModule)
  have h23 := L6.smithL6E23_of hMF hModule
  have h24 := L6.smithL6E24_of hMF hModule
  have h25 := L6.smithL6E25_of hMF hModule
  have h23f := L6.smithL6E23Four_of hF hModel h33 h34a h34b h24
  have hLoc := L6.smithL62LocalInput_of h34a h34b h23 h24 h25 h23f
  have hE := L6Ident.smithL6E23a_of h25 h34a h34b hLoc hC
    (fun _ _ h => L6Ident.exists_mem_T6_pair h) L6Ident.isSimpleGroup_closure_std
    (by rw [L6Ident.card_closure_std]; norm_num)
  have hLine := L6.smithL6E24Line_of hMF hModule
  have h261 := L6Ident.smithL6E261_of h34a h34b hLoc hE hC h33 hF (fun i hi => hMF.wt_ne_zero hi)
    L6Ident.hF3_holds (fun _ _ h => LMod.card_closure_commSet_ge h)
  have hPath := L6.smithL62PathInput_of h34a h34b h23 h24 h25 h23f hLine
    (L6.smithL6E421Three_of h34a h261)
  exact partB_of_local_path hAS hDW hHolt hLoc hPath

theorem partA_partB_of_gh74
    (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) :
    PartA ∧ PartB :=
  ⟨partA_of_reifartSmithU62Input (Yardstones.M3aba7dc4b8a8.reifartSmithU62Input_of_gh74 hgh),
    partB_of_gh74_only hgh⟩

end CFSG.GF2Type.SmithTypeE
