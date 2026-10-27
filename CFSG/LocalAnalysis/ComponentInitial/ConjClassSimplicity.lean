module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem conjugacy_class_divisor_simplicity {G : Type*} [Group G] [Finite G]
    (hG : 1 < Nat.card G) {m : ℕ} (C : Fin m → ConjClasses G) (hCinj : Function.Injective C)
    (hCrange : ∀ c : ConjClasses G, c ∈ Set.range C ↔ c ≠ ConjClasses.mk 1)
    (hdiv : ∀ I : Finset (Fin m), (1 + ∑ i ∈ I, (C i).carrier.ncard) ∣ Nat.card G →
      1 + ∑ i ∈ I, (C i).carrier.ncard = 1 ∨ 1 + ∑ i ∈ I, (C i).carrier.ncard = Nat.card G) :
    Nontrivial G ∧ IsSimpleGroup G := by
  classical
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hG
  have : Fintype G := Fintype.ofFinite G
  refine ⟨hnt, ⟨fun N hN => ?_⟩⟩
  set I := Finset.univ.filter (fun i => (C i).carrier ⊆ (N : Set G)) with hI
  have hne1 : ∀ i, (1 : G) ∉ (C i).carrier := fun i h1 =>
    ((hCrange (C i)).1 ⟨i, rfl⟩) ((ConjClasses.mem_carrier_iff_mk_eq).1 h1).symm
  have hset : (N : Set G) = {1} ∪ ⋃ i ∈ I, (C i).carrier := by
    ext g
    constructor
    · intro hg
      by_cases h1 : g = 1
      · exact Or.inl h1
      · right
        have hgc : ConjClasses.mk g ≠ ConjClasses.mk 1 := fun h =>
          h1 (isConj_one_left.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h))
        obtain ⟨i, hi⟩ := (hCrange (ConjClasses.mk g)).2 hgc
        refine Set.mem_biUnion (x := i) ?_ ?_
        · rw [hI, Finset.coe_filter]
          refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
          rw [ConjClasses.mem_carrier_iff_mk_eq, hi, ConjClasses.mk_eq_mk_iff_isConj] at hx
          obtain ⟨c, hc⟩ := isConj_iff.1 hx.symm
          rw [← hc]
          exact hN.conj_mem g hg c
        · rw [hi]
          exact ConjClasses.mem_carrier_mk
    · rintro (h | h)
      · rw [Set.mem_singleton_iff.1 h]
        exact N.one_mem
      · obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 h
        exact (Finset.mem_filter.1 hi).2 hgi
  have hU : (⋃ i ∈ I, (C i).carrier) = ↑(I.biUnion fun i => (C i).carrier.toFinset) := by
    ext g
    simp
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (C i).carrier.toFinset (C j).carrier.toFinset := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hxi hxj
    exact hij (hCinj (hxi.symm.trans hxj))
  have hcard : Nat.card N = 1 + ∑ i ∈ I, (C i).carrier.ncard := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_union_eq, Set.ncard_singleton,
      hU, Set.ncard_coe_finset, Finset.card_biUnion hdisj]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Set.ncard_eq_toFinset_card']
    · rw [Set.disjoint_singleton_left]
      intro h
      obtain ⟨i, -, h1⟩ := Set.mem_iUnion₂.1 h
      exact hne1 i h1
  rcases hdiv I (hcard ▸ Subgroup.card_subgroup_dvd_card N) with h | h
  · left
    exact Subgroup.eq_bot_of_card_eq N (hcard.trans h)
  · right
    exact Subgroup.eq_top_of_card_eq N (hcard.trans h)

end CFSG.LocalAnalysis.ComponentInitial
