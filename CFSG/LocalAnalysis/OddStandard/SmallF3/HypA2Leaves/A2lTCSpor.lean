module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporTable
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GS82PumpInputs
open CFSG.ComponentClassification.HarrisLit.T1.SporRow

section Dispatch


theorem a2l_spor_arm {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) : NativeSporadic.IsSporadic S .HS := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hMcard := Open.Open.monster_y443_derived_card
  have hO := a2l_oddLieOrder_of_tcSmall hS
  cases s
  case HS => exact ⟨e⟩
  all_goals exfalso
  case M11 => exact a2l_false_of_m11 e h hS
  case M12 => exact a2l_false_of_m12 e h hS
  case M22 => exact a2l_false_of_m22 e h hS
  case M23 => exact a2l_false_of_m23 e h hS
  case M24 => exact a2l_false_of_m24 e h hS
  case J1 => exact a2l_false_of_j1 hna e h hS
  case J2 => exact a2l_false_of_j2 e h hS
  case J3 => exact a2l_false_of_j3 e h hS
  case He => exact a2l_false_of_he hna e h hS
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
    exact SporTable.false_of_tableExcl hMcard BMCase.sporadicOddCoreFree_B
      SporTable.tableExcl_B hna e h hO
  case M =>
    exact SporTable.false_of_tableExcl hMcard CatalogueU.sporadicOddCoreFree_M
      SporTable.tableExcl_M hna e h hO
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

end Dispatch

end CFSG.OddStandard.SmallF3.HypA2Leaves
