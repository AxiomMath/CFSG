module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.D43

theorem mem_of_partition {α : Type*} [DecidableEq α] {n : ℕ} (A : Fin n → Finset α)
    (S : Finset α) (f : Fin n → ℕ) (hAS : ∀ i, A i ⊆ S)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hf : ∀ i, (A i).card = f i) (hsum : ∑ i, f i = S.card) : ∀ q ∈ S, ∃ i, q ∈ A i := by
  have hU : Finset.univ.biUnion A = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hq
      exact hAS j hj
    · rw [Finset.card_biUnion (by intro x _ y _ hxy; exact hdisj x y hxy), ← hsum]
      exact (Finset.sum_congr rfl fun j _ => hf j).ge
  intro q hq
  rw [← hU] at hq
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hq
  exact ⟨j, hj⟩

theorem orbit_eq_of_partition {H α : Type*} [Group H] [Finite H] [MulAction H α] {n N : ℕ}
    (r : Fin n → α) (A : Fin n → Finset α) (S : Finset α) (f : Fin n → ℕ)
    (hA : ∀ i, (A i : Set α) ⊆ MulAction.orbit H (r i))
    (hS : ∀ i, MulAction.orbit H (r i) ⊆ S)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hf : ∀ i, (A i).card = f i) (hsum : ∑ i, f i = S.card) (hN : Nat.card H ∣ N)
    (hdiv : ∀ C : Finset (Fin n), 2 ≤ C.card → ¬ (∑ j ∈ C, f j) ∣ N) :
    ∀ i, MulAction.orbit H (r i) = A i := by
  classical
  have hcardU : ∀ C : Finset (Fin n), (C.biUnion A).card = ∑ j ∈ C, f j := by
    intro C
    rw [Finset.card_biUnion (by intro x _ y _ hxy; exact hdisj x y hxy)]
    exact Finset.sum_congr rfl fun j _ => hf j
  have hU : Finset.univ.biUnion A = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hq
      exact hS j (hA j hj)
    · rw [hcardU, hsum]
  intro i
  set C := Finset.univ.filter fun j => MulAction.orbit H (r j) = MulAction.orbit H (r i) with hC
  have horb : MulAction.orbit H (r i) = ↑(C.biUnion A) := by
    ext q
    rw [Finset.coe_biUnion]
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · intro hq
      have hqS : q ∈ S := hS i hq
      rw [← hU] at hqS
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hqS
      refine ⟨j, ?_, hj⟩
      rw [hC, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← MulAction.orbit_eq_iff.2 hq]
      exact (MulAction.orbit_eq_iff.2 (hA j hj)).symm
    · rintro ⟨j, hj, hqj⟩
      rw [hC, Finset.mem_filter] at hj
      rw [← hj.2]
      exact hA j hqj
  have hdvd : Nat.card (MulAction.orbit H (r i)) ∣ N := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact (Subgroup.index_dvd_card _).trans hN
  rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset, hcardU] at hdvd
  have hiC : i ∈ C := by
    rw [hC, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hC1 : C.card ≤ 1 := by
    by_contra hc
    exact hdiv C (by omega) hdvd
  have hCi : C = {i} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨hiC, fun j hj => Finset.card_le_one.1 hC1 j hj i hiC⟩
  rw [horb, hCi, Finset.singleton_biUnion]

theorem orbit_subset_of_le {G α : Type*} [Group G] [MulAction G α] {K L : Subgroup G}
    (hKL : K ≤ L) (x : α) : MulAction.orbit ↥K x ⊆ MulAction.orbit ↥L x := by
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  exact ⟨⟨k, hKL hk⟩, rfl⟩

end CFSG.KC.D43

end
