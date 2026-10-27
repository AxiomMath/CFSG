module

public import CFSG.GH74.GLS.Bg.Pu5.L299MStatements
public import CFSG.GH74.GLS.Bg.Pu5.L299Swap
public import CFSG.GH74.GLS.Bg.Pu5.L299FStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem l299four_of (h44 : II4_44) (hquat : II4_4_quat) (h293 : L293) (hF1 : L299F1) (hF2 : L299F2) :
    L299FourS := by
  intro G _ _ z t S hC hcard K hK h4 hnc
  obtain ⟨S', hC', hcard', hiso⟩ := cfg_swap_data h44 hquat h293 hC hcard
  obtain ⟨K', hK'⟩ := rigid_nonempty hC'.hz hC'.hzK
  obtain ⟨e⟩ := hiso K hK K' hK'
  have h4' : Nat.card ↥(S' ⊓ cSec K') = 4 := by
    rw [← Nat.card_congr e.toEquiv]
    exact h4
  have hnc' : ¬ IsCyclic ↥(S' ⊓ cSec K') := fun h => hnc (e.isCyclic.2 h)
  obtain ⟨s, hsC, hss⟩ := hF1 G t z S' hC' hcard' K' hK' h4' hnc'
  exact hF2 G z t S hC hcard K hK h4 hnc ⟨s, hsC, hss⟩

end CFSG.GH74.GLS.Bg.Pu5
