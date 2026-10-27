module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Criterion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

structure RowData (Y : Type*) [Group Y] [Finite Y] : Prop where
  hypothesisOne : HypothesisOne Y
  rank : 3 ≤ CFSG.Open.twoRank Y

theorem RowData.of_elemAbelian_eight {Y : Type*} [Group Y] [Finite Y] (hI : HypothesisOne Y)
    (E : Subgroup Y) (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 8) : RowData Y :=
  ⟨hI, three_le_twoRank_of_elemAbelian_eight E hE hcard⟩

theorem card_sylow_eq_two_of_stdHyp {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hI : HypothesisOne (L ⧸ center L))
    (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L)) (h25 : Asc76Lemma25)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have := h.simple
  obtain ⟨S₀, hS₀⟩ := h.cyclicSylow
  let f : S₀ ≃* S := Sylow.equiv S₀ S
  have hS : IsCyclic S := isCyclic_of_surjective f.toMonoidHom f.surjective
  exact card_sylow_eq_two_of_simple h.nonabelian h.standard S hS hI hrank h25

theorem card_sylow_eq_two_of_rowData {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hrow : RowData (L ⧸ center L)) (h25 : Asc76Lemma25)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  card_sylow_eq_two_of_stdHyp h hrow.hypothesisOne hrow.rank h25 S

theorem card_sylow_eq_two_of_stdHyp_of_nodeCriterion {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : StdHyp G L) (hOut : (innAut (L ⧸ center L)).index ∣ 2)
    (hcrit : NodeCriterion (L ⧸ center L)) (hrank : 3 ≤ CFSG.Open.twoRank (L ⧸ center L))
    (h25 : Asc76Lemma25) (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  card_sylow_eq_two_of_stdHyp h (hypothesisOne_of_nodeCriterion hOut hcrit) hrank h25 S

end CFSG.EvenSporadicStandard.Finkelstein77
