module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeHyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeCentre
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeStandard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeBalanced
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.BridgeRank
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem fritzHyp_of_smallF3
    (hGH74 : UFrontier.GH74ModelsInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : SmallF3Cyclic G L) (hC : ¬ Blueprint.Catalog G)
    (hL : LieModel (L ⧸ center L) .PSL 3 3 1) : ∃ t : G, FritzHyp G t L := by
  have hZ := center_eq_bot_of_l33 hS hL
  obtain ⟨t, ht, ht2⟩ := exists_involution_of_standard' hS.standard
  have hLt := le_centralizer_of_mem_centralizer ht
  have hmodel := lieModel_of_center_eq_bot hZ hL
  have htL : t ∉ L := by
    intro htL
    have hc : (⟨t, htL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hLt g.2)
    rw [hZ, mem_bot] at hc
    have h1 : t = 1 := congrArg Subtype.val hc
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  haveI := hS.simple
  exact ⟨t, {
    orderOf_t := ht2
    model := hmodel
    isSimple := isSimple_of_standard_of_center_eq_bot hS.standard hZ
    le_centralizer := hLt
    le_normalizer := centralizer_le_normalizer_of_standard hS.standard ht ht2
    isCyclic_C := hS.cyclic
    isPGroup_K := isPGroup_inf_of_balanced hS.standard (hS.balanced t ht2) hS.cyclic ht ht2
    not_sectRank4 := fun hs => hC (UFrontier.catalog_of_gh74 hGH74 hS.nonab
      (three_le_twoRank_of_l33 hmodel hLt ht2 htL) hs) }⟩

end CFSG.OddStandard.SmallF3.L33
