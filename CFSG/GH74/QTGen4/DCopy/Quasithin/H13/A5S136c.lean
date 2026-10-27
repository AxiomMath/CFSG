module

public import CFSG.Quasithin.H13.A5S136c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma_13_6_26_one_F4 (h1338 : A6.Stmt13_3_8_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hO2 : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hKH : K ≤ H := le_of_mem_cComp hK

  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have h121' : (K.subgroupOf H).Normal ∨ (conjSubgroupsBy H K).ncard = 2 := by
    rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK with h | h
    · exact Or.inl h
    · exact Or.inr h.1

  have hYM : conjClosure K H ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_of_two hTsyl S.T_le_NL hKH hKM h121'
  have hYH : conjClosure K H ≤ H := conjClosure_le fun h hh k hk =>
    H.mul_mem (H.mul_mem hh (hKH hk)) (H.inv_mem hh)
  have hYperf : ⁅conjClosure K H, conjClosure K H⁆ = conjClosure K H :=
    conjClosure_perfect (perfect_of_mem_cComp hK)
  have hYO2 : oTwoRes (conjClosure K H) = conjClosure K H := by
    rw [oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_eq_of_perfect' hYperf

  obtain ⟨-, h23⟩ := h1338 G T L L H (conjClosure K H) S.h13 S.h13.faithful ⟨hTH, hO2⟩ hHM hYO2
    hYH (le_normalizer_conjClosure K H) hYM
  have hsolv := isSolvable_of_isTwoThreeGroup h23
  have hKY : K ≤ conjClosure K H := le_conjClosure K H
  exact not_isSolvable_of_mem_cComp hK
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKY)
      (Subgroup.inclusion_injective hKY))

end Setting

end CFSG.Quasithin.H13.A5
