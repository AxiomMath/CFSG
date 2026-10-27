module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRCover
public import CFSG.RankThree.PartOne.S11c.Co1Cover

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree

theorem k37R_coverRankFour_GA :
    K37RCoverRankFour ↥GA := by
  intro Y _ _ π hπ hker
  let Y' : Subgroup Y := ⊤
  let π' : ↥Y' →* ↥GA := π.comp Y'.subtype
  have hπ' : Function.Surjective π' := by
    intro g
    obtain ⟨y, hy⟩ := hπ g
    exact ⟨⟨y, trivial⟩, hy⟩
  have hker' : π'.ker ≤ Subgroup.center ↥Y' := by
    intro x hx
    have hx' : (x : Y) ∈ Subgroup.center Y := hker hx
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hx' (g : Y))
  have hcomm := co1_commute_of_mem_comap π' hπ' hker'
  set D : Subgroup GA := (E ⊓ Subgroup.centralizer {c 0}).subgroupOf GA with hD
  have hDle : D ≤ E.subgroupOf GA := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hDcard : 3 ^ 4 ≤ Nat.card D := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans co1_E_le_GA)).toEquiv, co1_card_centralizer]
  have hDp : ∀ x ∈ D, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact E_pow_three _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1)
  have hF : ∀ x ∈ D.comap π', ∀ y ∈ D.comap π', x * y = y * x := fun x hx y hy =>
    hcomm x (Subgroup.comap_mono hDle hx) y (Subgroup.comap_mono hDle hy)
  have hz : orderOf (co1CS 0) = 2 := by
    rw [co1CS, Subgroup.orderOf_mk]
    exact co1_orderOf_c_zero
  have hzD : ∀ x ∈ D, Commute (co1CS 0) x := fun x hx => by
    have := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact Subtype.ext this.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.central_cover_involution_witness Y' hπ' hker' Nat.prime_three
      (by norm_num) hDp hF hDcard hz hzD
  exact hrank

theorem k37R_coverRankFour_Co1 :
    K37RCoverRankFour CFSG.Blueprint.NativeSporadic.Co1 :=
  k37R_coverRankFour_GA.of_mulEquiv co1GAEquiv

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
