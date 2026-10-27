module

public import CFSG.GroupTheory.SteinbergBKCoprimeHallConjugacy

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem solvable_coprime_invariant_hall_containment {A H : Type*} [Group A] [Group H] [Finite A]
    [Finite H] [MulDistribMulAction A H] (hH : Group.IsSolvable H)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H)) (π : Set Nat.Primes) (U : Subgroup H)
    (hUπ : IsPiSubgroup π U) (hU : ∀ a : A, ∀ x ∈ U, a • x ∈ U) :
    ∃ K : Subgroup H, IsHallSubgroup π K ∧ (∀ a : A, ∀ x ∈ K, a • x ∈ K) ∧ U ≤ K := by
  obtain ⟨K, hK, hKinv, hUK⟩ := CFSG.exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := A) hH hcop π U hUπ (isInvariant_of_smul_mem hU)
  exact ⟨K, hK, fun a x hx => (hKinv.invariant a x).1 hx, hUK⟩

end CFSG.GroupTheory.SteinbergBK
