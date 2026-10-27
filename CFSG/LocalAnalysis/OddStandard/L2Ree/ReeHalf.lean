module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.Halves
public import CFSG.LocalAnalysis.OddStandard.L2Ree.Mult
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructure
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureStdHyp
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureUnbalanced
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Main

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification


theorem ree_half (hW : CFSG.EvenSporadicStandard.J1Std.WalterAbelian)
    (hGA : GriessAllModelsStatement) (hB : TauCetiBridge.TypewiseBridges) : ReeHalf := by
  intro G _ _ L hS hU hlie S hcyc
  obtain ⟨f, hm⟩ := hlie
  by_cases hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  · rcases ree_unbalanced hS hm (hU hz) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exfalso
    have hZ : center L = ⊥ :=
      ree_center_trivial hGA hB
        ((AssemblyBPredicates.isQuasisimple_iff_native _).mp hS.standard.1) hm
    have hstd := stdHyp_of_not_unbalanced hS hz ⟨S, hcyc⟩ hZ
    obtain ⟨t, ht, ht2⟩ := CFSG.OddStandard.exists_involution_of_standard hS.standard
    obtain ⟨E, M, hEL, hE8, hE2, hEsyl, hEC, hEN, hLM, hMN, hModd, hMC, hMd, -⟩ :=
      exists_ree_structure hstd hm hZ ht ht2
    exact CFSG.EvenSporadicStandard.ReeStd.false_of_setting hW
      { z := t, L := L, M := M, E := E, simple := hS.simple, nonabelian := hS.nonab,
        order_z := ht2, E_le := hEL, card_E := hE8, sq_E := hE2, sylow_E := hEsyl,
        centralizer_E := hEC, card_normalizer_E := hEN, L_le := hLM, L_normal := hMN,
        odd_relIndex := hModd, centralizer_eq := hMC, disjoint := hMd }

end CFSG.OddStandard.L2Ree
