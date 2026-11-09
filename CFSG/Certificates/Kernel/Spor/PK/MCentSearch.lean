module

public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.KS.MCent

open CFSG.Sporadic.Schreier

variable {M : Type*} [Monoid M]

@[expose] def prCnt (tst : Nat → M → Bool) (leaf : M → Bool) : Nat → List (List M) → M → Nat
  | _, [], p => if leaf p then 1 else 0
  | l, T :: Ts, p => (T.map fun t => if tst l (p * t) then prCnt tst leaf (l + 1) Ts (p * t) else 0).sum

theorem prCnt_eq (tst : Nat → M → Bool) (leaf : M → Bool) :
    ∀ (Ts : List (List M)) (l : Nat) (p : M),
      (∀ k < Ts.length, ∀ q, ∀ x ∈ products (Ts.drop (k + 1)), leaf (q * x) = true →
        tst (l + k) q = true) →
      prCnt tst leaf l Ts p = (products Ts).countP fun x => leaf (p * x)
  | [], l, p, _ => by simp [prCnt, products]
  | T :: Ts, l, p, H => by
    rw [prCnt, products, List.countP_flatMap]
    refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    rw [Function.comp_apply, List.countP_map]
    by_cases ht : tst l (p * t) = true
    · rw [ite_eq_left ht, prCnt_eq tst leaf Ts (l + 1) (p * t) fun k hk q x hx hl => by
        have := H (k + 1) (by simp; omega) q x (by simpa using hx) hl
        rwa [Nat.add_assoc, Nat.add_comm 1 k]]
      exact List.countP_congr fun x _ => by simp [Function.comp, mul_assoc]
    · rw [ite_eq_right ht]
      refine (List.countP_eq_zero.2 fun x hx hl => ht ?_).symm
      have := H 0 (by simp) (p * t) x (by simpa using hx) (by simpa [mul_assoc] using hl)
      simpa using this

section ClassEq

variable {G : Type*} [Group G]

theorem card_conj_mul_cent [Finite G] (g : G) :
    ({x | IsConj x g} : Set G).ncard * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  have h1 := (MulAction.stabilizer (ConjAct G) g).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have e : MulAction.orbit (ConjAct G) g = {x | IsConj x g} := by
    ext x
    exact ConjAct.mem_orbit_conjAct
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, ← e, Nat.mul_comm, h1]
  exact Nat.card_congr ConjAct.toConjAct.toEquiv.symm

theorem classEq_cover [Finite G] {N : ℕ} (r : ℕ → G) (c : ℕ → ℕ)
    (hc : ∀ i < N, Nat.card (Subgroup.centralizer {r i}) ≤ c i)
    (hnc : ∀ i < N, ∀ j < N, i < j → ¬ IsConj (r i) (r j))
    (hsum : ∑ i ∈ Finset.range N, Nat.card G / c i = Nat.card G) :
    (∀ x, ∃ i < N, IsConj x (r i)) ∧
      ∀ i < N, ({x | IsConj x (r i)} : Set G).ncard = Nat.card G / c i := by
  classical
  cases nonempty_fintype G
  set C : ℕ → Finset G := fun i => Finset.univ.filter fun x => IsConj x (r i)
  have hC : ∀ i, (C i).card = ({x | IsConj x (r i)} : Set G).ncard := fun i => by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [C]
  have hcard : ∀ i, (C i).card = Nat.card G / Nat.card (Subgroup.centralizer {r i}) := fun i => by
    rw [hC, ← card_conj_mul_cent (r i), Nat.mul_div_cancel _ Nat.card_pos]
  have hge : ∀ i ∈ Finset.range N, Nat.card G / c i ≤ (C i).card := fun i hi => by
    rw [hcard]
    exact Nat.div_le_div_left (hc i (Finset.mem_range.1 hi)) Nat.card_pos
  have hdisj : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hnc i hi j hj h (hxi.symm.trans hxj)
    · exact hnc j hj i hi h (hxj.symm.trans hxi)
  have hU := Finset.card_biUnion hdisj
  have hle : ((Finset.range N).biUnion C).card ≤ Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  have hS : ∑ i ∈ Finset.range N, (C i).card = ∑ i ∈ Finset.range N, Nat.card G / c i := by
    refine le_antisymm ?_ (Finset.sum_le_sum hge)
    rw [hsum, ← hU]
    exact hle
  have hall : (Finset.range N).biUnion C = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hU, hS, hsum, Nat.card_eq_fintype_card]
  refine ⟨fun x => ?_, fun i hi => ?_⟩
  · have hx : x ∈ (Finset.range N).biUnion C := by
      rw [hall]
      exact Finset.mem_univ x
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hxi
    exact ⟨i, Finset.mem_range.1 hi, hxi⟩
  · rw [← hC]
    exact ((Finset.sum_eq_sum_iff_of_le hge).1 hS.symm i (Finset.mem_range.2 hi)).symm

theorem classEq_sum [Fintype G] {N : ℕ} (r : ℕ → G) (c : ℕ → ℕ)
    (hc : ∀ i < N, Nat.card (Subgroup.centralizer {r i}) ≤ c i)
    (hnc : ∀ i < N, ∀ j < N, i < j → ¬ IsConj (r i) (r j))
    (hsum : ∑ i ∈ Finset.range N, Nat.card G / c i = Nat.card G) (f : G → ℕ)
    (hf : ∀ x y, IsConj x y → f x = f y) :
    ∑ x, f x = ∑ i ∈ Finset.range N, Nat.card G / c i * f (r i) := by
  classical
  obtain ⟨hcov, hsz⟩ := classEq_cover r c hc hnc hsum
  set C : ℕ → Finset G := fun i => Finset.univ.filter fun x => IsConj x (r i)
  have hdisj : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j → Disjoint (C i) (C j) := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hxi hxj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hnc i hi j hj h (hxi.symm.trans hxj)
    · exact hnc j hj i hi h (hxj.symm.trans hxi)
  have hall : (Finset.range N).biUnion C = Finset.univ := by
    refine Finset.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi, hxi⟩ := hcov x
    exact Finset.mem_biUnion.2
      ⟨i, Finset.mem_range.2 hi, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxi⟩⟩
  rw [← hall, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hC : (C i).card = Nat.card G / c i := by
    rw [← hsz i (Finset.mem_range.1 hi), ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [C]
  rw [Finset.sum_congr rfl fun x hx => hf x (r i) (Finset.mem_filter.1 hx).2, Finset.sum_const,
    smul_eq_mul, hC]

end ClassEq

end CFSG.KS.MCent

end
