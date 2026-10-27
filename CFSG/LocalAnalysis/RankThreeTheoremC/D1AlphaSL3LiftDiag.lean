module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix

open Polynomial in
private theorem exists_lagrange_components {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (m : A) (r : Fin 3 → k) (hr : Function.Injective r)
    (hm : (m - r 0 • (1 : A)) * (m - r 1 • 1) * (m - r 2 • 1) = 0) :
    ∃ E : Fin 3 → A, ∑ i, E i = 1 ∧ (∀ i, m * E i = r i • E i) ∧
      ∀ x : A, Commute x m → ∀ i, Commute x (E i) := by
  classical
  refine ⟨fun i => aeval m (Lagrange.basis Finset.univ r i), ?_, ?_, ?_⟩
  · rw [← map_sum, Lagrange.sum_basis hr.injOn Finset.univ_nonempty, map_one]
  · intro i
    have key : (X - C (r i)) * Lagrange.basis Finset.univ r i =
        C (Lagrange.nodalWeight Finset.univ r i) * Lagrange.nodal Finset.univ r := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
        ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
        Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
      ring
    have hm' : (m - algebraMap k A (r 0)) * (m - algebraMap k A (r 1)) *
        (m - algebraMap k A (r 2)) = 0 := by
      simpa [Algebra.algebraMap_eq_smul_one] using hm
    have h := congrArg (aeval m) key
    simp only [map_mul, map_sub, aeval_X, aeval_C, Lagrange.nodal_eq, Fin.prod_univ_three,
      hm', mul_zero] at h
    rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul]
    exact h
  · intro x hx i
    exact Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton k m) hx

private theorem invOf_mul_mul_eq_diagonal {k : Type*} [Field k] (M P : Matrix (Fin 3) (Fin 3) k)
    [Invertible P] (a : Fin 3 → k) (h : M * P = P * Matrix.diagonal a) :
    ⅟P * M * P = Matrix.diagonal a := by
  rw [mul_assoc, h, ← mul_assoc, invOf_mul_self, one_mul]

theorem exists_joint_diagonal {k : Type*} [Field k] (M N : Matrix (Fin 3) (Fin 3) k)
    (hMN : M * N = N * M) (r t : Fin 3 → k) (hr : Function.Injective r)
    (ht : Function.Injective t)
    (hM : (M - r 0 • (1 : Matrix (Fin 3) (Fin 3) k)) * (M - r 1 • 1) * (M - r 2 • 1) = 0)
    (hN : (N - t 0 • (1 : Matrix (Fin 3) (Fin 3) k)) * (N - t 1 • 1) * (N - t 2 • 1) = 0) :
    ∃ P : GL (Fin 3) k, ∃ a b : Fin 3 → k,
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * M * (P : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal a ∧
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * N * (P : Matrix (Fin 3) (Fin 3) k) =
        Matrix.diagonal b := by
  classical
  obtain ⟨E, hEsum, hEeig, -⟩ := exists_lagrange_components M r hr hM
  obtain ⟨F, hFsum, hFeig, hFcomm⟩ := exists_lagrange_components N t ht hN
  let S : Set (Fin 3 → k) := {w | ∃ i j, M *ᵥ w = r i • w ∧ N *ᵥ w = t j • w}
  have hmem : ∀ (v : Fin 3 → k) (i j : Fin 3), (F j * E i) *ᵥ v ∈ S := by
    intro v i j
    refine ⟨i, j, ?_, ?_⟩
    · have h1 : M * (F j * E i) = r i • (F j * E i) := by
        rw [← mul_assoc, (hFcomm M hMN j).eq, mul_assoc, hEeig i, mul_smul_comm]
      rw [mulVec_mulVec, h1, smul_mulVec]
    · have h1 : N * (F j * E i) = t j • (F j * E i) := by
        rw [← mul_assoc, hFeig j, smul_mul_assoc]
      rw [mulVec_mulVec, h1, smul_mulVec]
  have hspan : Submodule.span k S = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hv : v = ∑ j, ∑ i, (F j * E i) *ᵥ v := by
      calc v = (1 : Matrix (Fin 3) (Fin 3) k) *ᵥ v := (one_mulVec v).symm
        _ = ((∑ j, F j) * (∑ i, E i)) *ᵥ v := by rw [hFsum, hEsum, one_mul]
        _ = ∑ j, ∑ i, (F j * E i) *ᵥ v := by
          rw [Finset.sum_mul_sum, sum_mulVec]
          exact Finset.sum_congr rfl fun j _ => sum_mulVec _ _ _
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span (hmem v i j)
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent k S
  have hbtop : ⊤ ≤ Submodule.span k (Set.range ((↑) : b → (Fin 3 → k))) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb : Module.Basis b k (Fin 3 → k) := Module.Basis.mk hbli hbtop
  let e : b ≃ Fin 3 := bb.indexEquiv (Pi.basisFun k (Fin 3))
  let bas : Module.Basis (Fin 3) k (Fin 3 → k) := bb.reindex e
  have hbas : ∀ j, bas j ∈ S := by
    intro j
    simp only [bas, Module.Basis.reindex_apply, bb, Module.Basis.mk_apply]
    exact hbS (e.symm j).2
  choose i₁ i₂ h1 h2 using hbas
  let P : Matrix (Fin 3) (Fin 3) k := (Pi.basisFun k (Fin 3)).toMatrix bas
  let _ : Invertible P := Module.Basis.invertibleToMatrix _ _
  have hP : ∀ i j, P i j = bas j i := by
    intro i j
    simp [P, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hcol : ∀ (X : Matrix (Fin 3) (Fin 3) k) (c : Fin 3 → k),
      (∀ j, X *ᵥ bas j = c j • bas j) → X * P = P * Matrix.diagonal c := by
    intro X c hX
    ext i j
    have := congrFun (hX j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply, mul_comm (P i j)]
    simp only [hP]
    exact this
  refine ⟨unitOfInvertible P, fun j => r (i₁ j), fun j => t (i₂ j), ?_, ?_⟩
  · rw [val_inv_unitOfInvertible, val_unitOfInvertible]
    exact invOf_mul_mul_eq_diagonal M P _ (hcol M _ h1)
  · rw [val_inv_unitOfInvertible, val_unitOfInvertible]
    exact invOf_mul_mul_eq_diagonal N P _ (hcol N _ h2)

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
