module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem ncard_conjugatesOf_mul_card_centralizer (x : G) :
    (conjugatesOf x).ncard * Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  rw [mul_comm, ← Subgroup.index_centralizer_eq_ncard, Subgroup.card_mul_index]

theorem ncard_conjugatesOf_eq_div [Finite G] (x : G) :
    (conjugatesOf x).ncard = Nat.card G / Nat.card (Subgroup.centralizer ({x} : Set G)) :=
  (Nat.div_eq_of_eq_mul_left Nat.card_pos (ncard_conjugatesOf_mul_card_centralizer x).symm).symm

theorem card_centralizer_eq_of_isConj [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  have hx := ncard_conjugatesOf_mul_card_centralizer x
  have hy := ncard_conjugatesOf_mul_card_centralizer y
  rw [h.conjugatesOf_eq] at hx
  have hpos : 0 < (conjugatesOf y).ncard := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hy
    exact (Nat.card_pos (α := G)).ne' hy.symm
  exact Nat.eq_of_mul_eq_mul_left hpos (hx.trans hy.symm)

theorem ne_one_of_card_centralizer_ne [Finite G] {x : G}
    (h : Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ Nat.card G) : x ≠ 1 := by
  rintro rfl
  apply h
  have : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by simp
  rw [this, Subgroup.card_top]

theorem exists_isConj_of_sum_eq {ι : Type*} [Fintype ι] [Finite G] (r : ι → G) (s : Set G)
    (hs : ∀ x y, IsConj x y → y ∈ s → x ∈ s) (hr : ∀ i, r i ∈ s)
    (hne : ∀ i j, i ≠ j → Nat.card (Subgroup.centralizer ({r i} : Set G)) ≠
      Nat.card (Subgroup.centralizer ({r j} : Set G)))
    (hsum : ∑ i, Nat.card G / Nat.card (Subgroup.centralizer ({r i} : Set G)) = s.ncard) :
    ∀ x ∈ s, ∃ i, IsConj x (r i) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let K : ι → Finset G := fun i => (conjugatesOf (r i)).toFinset
  have hK : ∀ i x, x ∈ K i ↔ IsConj (r i) x := fun i x => Set.mem_toFinset
  have hdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      Disjoint (K i) (K j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [hK] at hxi hxj
    exact hne i j hij (card_centralizer_eq_of_isConj (hxi.trans hxj.symm))
  have hcardK : ∀ i, (K i).card = Nat.card G / Nat.card (Subgroup.centralizer ({r i} : Set G)) :=
    fun i => by
      rw [← ncard_conjugatesOf_eq_div, ← Set.ncard_coe_finset]
      simp [K]
  have hsub : (Finset.univ.biUnion K) ⊆ s.toFinset := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.1 hx
    rw [hK] at hxi
    exact Set.mem_toFinset.2 (hs x (r i) hxi.symm (hr i))
  have hcard : (Finset.univ.biUnion K).card = s.toFinset.card := by
    rw [Finset.card_biUnion hdisj]
    simp only [hcardK]
    rw [hsum]
    exact Set.ncard_eq_toFinset_card' s
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  intro x hx
  have : x ∈ Finset.univ.biUnion K := by rw [heq]; exact Set.mem_toFinset.2 hx
  obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.1 this
  exact ⟨i, ((hK i x).1 hxi).symm⟩

end CFSG.GroupTheory
