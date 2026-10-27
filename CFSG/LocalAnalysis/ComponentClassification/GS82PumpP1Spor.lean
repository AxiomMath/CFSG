module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporTable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf HarrisLit.T1.SporRow

theorem chevOddSporadicClause_holds
    : ChevOddSporadicClause := by
  intro S _ _ hS hna ⟨s, ⟨e⟩⟩ σ P h r hr hr2 ⟨τ, n, f, hL⟩ hnot
  have : IsSimpleGroup S := hS
  have hMcard := Open.Open.monster_y443_derived_card
  have hO := oddLieOrder_of_lieModel hr hr2 hL
  cases s
  case J3 => exact ⟨⟨e⟩, SporSmall.lieModel_of_j3 e h hr2 hL hnot⟩
  all_goals exfalso
  case M11 => exact SporSmall.false_of_m11 e h hr2 hL
  case M12 => exact SporSmall.false_of_m12 e h hr2 hL hnot
  case M22 => exact SporSmall.false_of_m22 e h hr2 hL hnot
  case M23 => exact SporSmall.false_of_m23 e h hr2 hL hnot
  case M24 => exact SporSmall.false_of_m24 e h hr2 hL hnot
  case J1 => exact SporSmall.false_of_j1 hna e h hr2 hL hnot
  case J2 => exact SporSmall.false_of_j2 e h hr2 hL hnot
  case He => exact SporTable.false_of_he hna e h hL hnot
  case HS =>
    exact SporTable.false_of_hs hMcard CatalogueU.sporadicOddCoreFree_HS hna e h hr hr2 hL hnot
  case Co1 =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Co1
      SporTable.tableExcl_Co1 hna e h hO
  case Co2 =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
      SporTable.tableExcl_Co2 hna e h hO
  case Co3 =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
      SporTable.tableExcl_Co3 hna e h hO
  case B =>
    exact SporTable.false_of_tableExcl hMcard BMCase.sporadicOddCoreFree_B SporTable.tableExcl_B hna
      e h hO
  case M =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_M SporTable.tableExcl_M
      hna e h hO
  case J4 =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_J4
      SporTable.tableExcl_J4 hna e h hO
  case Th =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.ThSchreier.sporadicOddCoreFree_Th
      SporTable.tableExcl_Th hna e h hO
  case HN =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.HNOddCore.sporadicOddCoreFree_HN
      SporTable.tableExcl_HN hna e h hO
  case McL =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_McL
      SporTable.tableExcl_McL hna e h hO
  case Fi22 =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Fi22
      SporTable.tableExcl_Fi22 hna e h hO
  case Fi23 =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Fi23
      SporTable.tableExcl_Fi23 hna e h hO
  case Fi24Prime =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Fi24Prime
      SporTable.tableExcl_Fi24Prime hna e h hO
  case Ly =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.LySchreier.sporadicOddCoreFree_Ly
      SporTable.tableExcl_Ly hna e h hO
  case Suz =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Suz
      SporTable.tableExcl_Suz hna e h hO
  case ONan =>
    exact SporTable.false_of_tableExcl hMcard Sporadic.ONOddCore.sporadicOddCoreFree_ONan
      SporTable.tableExcl_ONan hna e h hO
  case Ru =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_Ru
      SporTable.tableExcl_Ru hna e h hO

end CFSG.ComponentClassification.GS82PumpInputs
