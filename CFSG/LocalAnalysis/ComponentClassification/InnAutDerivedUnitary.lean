module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

theorem innAutDerived_le_primeFormD {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    innAutDerived (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤
      primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
  haveI : Finite K := h.finite
  haveI : IsMulCommutative (K ≃+* K) :=
    ⟨⟨fun σ τ => CFSG.ComponentClassification.UnbalancedCatalog.ringAut_commute σ τ⟩⟩
  rw [innAutDerived, sup_le_iff]
  constructor
  · intro α hα
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h (C : Matrix (Fin n) (Fin n) K) α).1 hα
    rw [primeFormD]
    exact ⟨⟨s, s.2.1⟩, rfl⟩
  · rw [← ker_primeFormFieldFactor h hC hn hq]
    intro α hα
    exact Abelianization.commutator_subset_ker (primeFormFieldFactor h hC hn hq) hα

theorem mem_primeFormD_of_mem_innAutDerived {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβ : β ∈ innAutDerived (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) :=
  innAutDerived_le_primeFormD h hC hn hq hβ

theorem exists_primeFormConjHom_of_mem_innAutDerived {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβ : β ∈ innAutDerived (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    ∃ A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K),
      β = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) A := by
  have hβD := mem_primeFormD_of_mem_innAutDerived h hC hn hq hβ
  rw [primeFormD] at hβD
  obtain ⟨A, hA⟩ := hβD
  exact ⟨A, hA.symm⟩

theorem exists_primeFormConjHom_pow_scalar_of_mem_primeFormD {ℓ f n p : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hn : 3 ≤ n)
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβ : β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K))
    (hβp : β ^ p = 1) :
    ∃ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (c : Kˣ),
      h.norm (c : K) = 1 ∧
        (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
        β = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) A := by
  obtain ⟨A, hA'⟩ := hβ
  have hA := hA'.symm
  have h1 : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_pow, ← hA, hβp, map_one, one_mul]
  obtain ⟨-, c, hc1, hc⟩ := (primeFormPsi_eq_one_iff h hC hn ⟨A ^ p, 1⟩).1 h1
  exact ⟨A, c, hc1, by rwa [SubgroupClass.coe_pow] at hc, hA⟩

theorem exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived {ℓ f n p : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβ : β ∈ innAutDerived (primeFormP h (C : Matrix (Fin n) (Fin n) K)))
    (hβp : β ^ p = 1) :
    ∃ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (c : Kˣ),
      h.norm (c : K) = 1 ∧
        (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
        β = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) A :=
  exists_primeFormConjHom_pow_scalar_of_mem_primeFormD h hC hn
    (mem_primeFormD_of_mem_innAutDerived h hC hn hq hβ) hβp

end CFSG.ComponentClassification.OuterAutomorphisms

end
