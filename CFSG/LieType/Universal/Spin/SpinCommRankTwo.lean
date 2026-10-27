module

public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem ι_mul_ι_mem_adjoin (Q : QuadraticForm K V) (b : Module.Basis (Fin 2) K V)
    (m₁ m₂ : V) :
    ι Q m₁ * ι Q m₂ ∈ Algebra.adjoin K {ι Q (b 0) * ι Q (b 1)} := by
  set z := ι Q (b 0) * ι Q (b 1) with hz
  have hzmem : z ∈ Algebra.adjoin K {z} := Algebra.subset_adjoin rfl
  have hsq : ∀ i : Fin 2, ι Q (b i) * ι Q (b i) ∈ Algebra.adjoin K {z} := fun i => by
    rw [CliffordAlgebra.ι_sq_scalar]
    exact Subalgebra.algebraMap_mem _ _
  have hswap : ι Q (b 1) * ι Q (b 0) ∈ Algebra.adjoin K {z} := by
    have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) (b 0) (b 1)
    have : ι Q (b 1) * ι Q (b 0) = algebraMap K _ (QuadraticMap.polar Q (b 0) (b 1)) - z := by
      rw [← h, hz]
      abel
    rw [this]
    exact Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ _) hzmem
  have hbasis : ∀ i j : Fin 2, ι Q (b i) * ι Q (b j) ∈ Algebra.adjoin K {z} := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hsq 0
    · exact hzmem
    · exact hswap
    · exact hsq 1
  have h₁ := b.sum_repr m₁
  have h₂ := b.sum_repr m₂
  rw [← h₁, ← h₂]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  refine Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (hbasis j i) _) _

theorem even_le_adjoin_of_finrank_two (Q : QuadraticForm K V) (b : Module.Basis (Fin 2) K V)
    {x : CliffordAlgebra Q} (hx : x ∈ even Q) :
    x ∈ Algebra.adjoin K {ι Q (b 0) * ι Q (b 1)} := by
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v h =>
    have h0 : v ∈ (1 : Submodule K (CliffordAlgebra Q)) := by simpa using h
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h0
    exact Subalgebra.algebraMap_mem _ _
  | add x y hx hy ihx ihy => exact Subalgebra.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ihx =>
    exact Subalgebra.mul_mem _ (ι_mul_ι_mem_adjoin Q b m₁ m₂) ihx

theorem spinGroup_comm_of_finrank_two [FiniteDimensional K V] (Q : QuadraticForm K V)
    (h : Module.finrank K V = 2) (x y : ↥(spinGroup Q)) : x * y = y * x := by
  let b : Module.Basis (Fin 2) K V := Module.finBasisOfFinrankEq K V h
  have hx := even_le_adjoin_of_finrank_two Q b (spinGroup.mem_even x.2)
  have hy := even_le_adjoin_of_finrank_two Q b (spinGroup.mem_even y.2)
  apply Subtype.ext
  change (x : CliffordAlgebra Q) * y = y * x
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact (Algebra.commute_of_mem_adjoin_self hx).symm).eq

end CFSG.LieType.Universal.Spin
