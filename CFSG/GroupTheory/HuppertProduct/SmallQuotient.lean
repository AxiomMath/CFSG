module

public import CFSG.GroupTheory.HuppertProduct.Mho
import CFSG.GroupTheory.HuppertProduct.Quotient
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory.HuppertProduct

open scoped commutatorElement

private theorem comm_of_card_eq_pow_le_two {Q : Type*} [Group Q] {p n : ℕ} [Fact p.Prime]
    (hQ : Nat.card Q = p ^ n) (hn : n ≤ 2) : ∀ a b : Q, a * b = b * a := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · have h1 : Nat.card Q = 1 := by simpa using hQ
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 h1).1
    intro a b
    exact Subsingleton.elim _ _
  · have h1 : Nat.card Q = p := by simpa using hQ
    have : IsCyclic Q := isCyclic_of_prime_card h1
    have : IsMulCommutative Q := inferInstance
    exact this.is_comm.comm
  · have : IsMulCommutative Q := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
    exact this.is_comm.comm

theorem commutator_le_mho_of_relIndex_le {G : Type*} [Group G] [Finite G] {S : Subgroup G} {p : ℕ}
    [Fact p.Prime] (h : (mho S p).relIndex S ≤ p ^ 2) : ⁅S, S⁆ ≤ mho S p := by
  have hcard : Nat.card (↥S ⧸ (mho S p).subgroupOf S) = (mho S p).relIndex S :=
    (Subgroup.index_eq_card ((mho S p).subgroupOf S)).symm
  have hexp : ∀ q : ↥S ⧸ (mho S p).subgroupOf S, q ^ p = 1 := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact pow_mem_mho s.2
  have hpg : IsPGroup p (↥S ⧸ (mho S p).subgroupOf S) := fun q => ⟨1, by simpa using hexp q⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
  have hle : p ^ n ≤ p ^ 2 := by
    rw [← hn, hcard]
    exact h
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hle
  have hcomm := comm_of_card_eq_pow_le_two hn hn2
  have key : ∀ a b : ↥S, ⁅a, b⁆ ∈ (mho S p).subgroupOf S := by
    intro a b
    refine (QuotientGroup.eq_one_iff _).1 ?_
    have hmk : ((⁅a, b⁆ : ↥S) : ↥S ⧸ (mho S p).subgroupOf S)
        = ⁅(a : ↥S ⧸ (mho S p).subgroupOf S), (b : ↥S ⧸ (mho S p).subgroupOf S)⁆ := by
      simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hmk]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  apply Subgroup.commutator_le.2
  intro x hx y hy
  have hxy := Subgroup.mem_subgroupOf.1 (key ⟨x, hx⟩ ⟨y, hy⟩)
  simpa [commutatorElement_def] using hxy

end CFSG.GroupTheory.HuppertProduct
