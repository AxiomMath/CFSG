module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open scoped commutatorElement

theorem commutator_le_range_conjAut {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) :
    commutator (MulAut (LinearFlag.projectiveSL n K)) ≤ (LinearFlag.conjAut n K).range := by
  rw [commutator, Subgroup.commutator_le]
  intro α _ β _
  rw [commutatorElement_def, ← LinearFlag.linearAutGroup_eq_range]
  exact OuterDerived.commutator_mem_linearAutGroup hn α β

theorem exists_conjAut_of_mem_commutator {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    {α : MulAut (LinearFlag.projectiveSL n K)}
    (hα : α ∈ commutator (MulAut (LinearFlag.projectiveSL n K))) :
    ∃ A : GL (Fin n) K, α = LinearFlag.conjAut n K A := by
  obtain ⟨A, hA⟩ := commutator_le_range_conjAut hn hα
  exact ⟨A, hA.symm⟩

theorem commutator_le_inner_two {K : Type} [Field K] [Finite K] :
    commutator (MulAut (LinearFlag.projectiveSL 2 K)) ≤
      (MulAut.conj : LinearFlag.projectiveSL 2 K →* MulAut (LinearFlag.projectiveSL 2 K)).range := by
  have hout : ∀ a b : Outer (LinearFlag.projectiveSL 2 K), a * b = b * a := fun a b =>
    (equivalence (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K)).symm.injective
      (by rw [map_mul, map_mul]; exact OuterDerived.outer_psl2_mul_comm K _ _)
  rw [commutator, Subgroup.commutator_le]
  intro α _ β _
  change ⁅α, β⁆ ∈ inner (LinearFlag.projectiveSL 2 K)
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' (inner (LinearFlag.projectiveSL 2 K))) ⁅α, β⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hout _ _

theorem commutator_le_range_conjAut_two {K : Type} [Field K] [Finite K] :
    commutator (MulAut (LinearFlag.projectiveSL 2 K)) ≤ (LinearFlag.conjAut 2 K).range := by
  intro α hα
  obtain ⟨x, rfl⟩ := commutator_le_inner_two hα
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 2 K x
  exact ⟨Matrix.SpecialLinearGroup.toGL g, LinearFlag.conjAut_toGL g⟩

theorem exists_conjAut_of_mem_commutator_two {K : Type} [Field K] [Finite K]
    {α : MulAut (LinearFlag.projectiveSL 2 K)}
    (hα : α ∈ commutator (MulAut (LinearFlag.projectiveSL 2 K))) :
    ∃ A : GL (Fin 2) K, α = LinearFlag.conjAut 2 K A := by
  obtain ⟨A, hA⟩ := commutator_le_range_conjAut_two hα
  exact ⟨A, hA.symm⟩

theorem exists_conjAut_of_mem_commutator_of_two_le {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 2 ≤ n) {α : MulAut (LinearFlag.projectiveSL n K)}
    (hα : α ∈ commutator (MulAut (LinearFlag.projectiveSL n K))) :
    ∃ A : GL (Fin n) K, α = LinearFlag.conjAut n K A := by
  rcases hn.eq_or_lt with rfl | h3
  · exact exists_conjAut_of_mem_commutator_two hα
  · exact exists_conjAut_of_mem_commutator h3 hα

theorem commutator_le_primeFormD {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    commutator (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ≤
      primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [commutator, Subgroup.commutator_le]
  intro α _ β _
  rw [commutatorElement_def]
  exact OuterDerived.commutator_mem_primeFormD h hn hq α β

theorem exists_primeFormConjHom_of_mem_commutator {p f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hα : α ∈ commutator (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) :
    ∃ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      α = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A := by
  obtain ⟨A, hA⟩ := commutator_le_primeFormD h hn hq hα
  exact ⟨A, hA.symm⟩

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
