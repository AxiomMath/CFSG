module

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Matrix

section Eigen

variable {K : Type*} [Field K] {n : ℕ}

theorem sum_range_succ_of_periodic {M : Type*} [AddCommGroup M] (g : ℕ → M) (p : ℕ)
    (h : g p = g 0) : ∑ j ∈ Finset.range p, g (j + 1) = ∑ j ∈ Finset.range p, g j := by
  have h1 := Finset.sum_range_succ g p
  have h2 := Finset.sum_range_succ' g p
  rw [h] at h1
  exact add_right_cancel (h2.symm.trans h1)

def eigProj (A : Matrix (Fin n) (Fin n) K) (ω : K) (p i : ℕ) (v : Fin n → K) : Fin n → K :=
  ∑ j ∈ Finset.range p, ω ^ (i * j) • ((A ^ j) *ᵥ v)

theorem mulVec_eigProj (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ} (hp : 0 < p)
    (hA : A ^ p = 1) (hω : ω ^ p = 1) (i : ℕ) (v : Fin n → K) :
    A *ᵥ eigProj A ω p i v = (ω ^ i)⁻¹ • eigProj A ω p i v := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hω
    exact zero_ne_one hω
  have key : ω ^ i • (A *ᵥ eigProj A ω p i v) = eigProj A ω p i v := by
    have h := sum_range_succ_of_periodic (fun j => ω ^ (i * j) • ((A ^ j) *ᵥ v)) p (by
      simp only [mul_zero, pow_zero, one_smul, Matrix.one_mulVec]
      rw [mul_comm, pow_mul, hω, one_pow, one_smul, hA, Matrix.one_mulVec])
    unfold eigProj
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ', smul_comm, smul_smul, ← pow_add,
      mul_add, mul_one]
  calc A *ᵥ eigProj A ω p i v = (ω ^ i)⁻¹ • (ω ^ i • (A *ᵥ eigProj A ω p i v)) :=
        (inv_smul_smul₀ (pow_ne_zero i hω0) _).symm
    _ = (ω ^ i)⁻¹ • eigProj A ω p i v := by rw [key]

theorem sum_eigProj (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ}
    (hω : IsPrimitiveRoot ω p) (hp : 0 < p) (v : Fin n → K) :
    ∑ i ∈ Finset.range p, eigProj A ω p i v = (p : K) • v := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hne : ω ^ j ≠ 1 := hω.pow_ne_one_of_pos_of_lt hj0 (Finset.mem_range.1 hj)
    have hpow : (ω ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h1 : (∑ i ∈ Finset.range p, (ω ^ j) ^ i) * (ω ^ j - 1) = (ω ^ j) ^ p - 1 :=
      geom_sum_mul _ _
    rw [hpow, sub_self] at h1
    have hgeom : ∑ i ∈ Finset.range p, ω ^ (i * j) = 0 := by
      simpa only [pow_mul'] using (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
    rw [hgeom, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hp) h

theorem top_le_span_eigenvectors (A : Matrix (Fin n) (Fin n) K) {ω : K} {p : ℕ}
    (hω : IsPrimitiveRoot ω p) (hp : 0 < p) (hpK : (p : K) ≠ 0) (hA : A ^ p = 1) :
    ⊤ ≤ Submodule.span K {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w} := by
  intro v _
  have hv : v = (p : K)⁻¹ • ∑ i ∈ Finset.range p, eigProj A ω p i v := by
    rw [sum_eigProj A hω hp v, inv_smul_smul₀ hpK]
  rw [hv]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_)
  exact ⟨_, mulVec_eigProj A hp hA hω.pow_eq_one i v⟩

end Eigen

section Basis

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_eigenbasis_matrix (A : Matrix (Fin n) (Fin n) K)
    (hspan : ⊤ ≤ Submodule.span K {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w}) :
    ∃ (P Q : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
      P * Q = 1 ∧ Q * P = 1 ∧ A * P = P * diagonal u := by
  classical
  let b0 := Module.Basis.ofSpan hspan
  let e := b0.indexEquiv (Pi.basisFun K (Fin n))
  let b := b0.reindex e
  have hb : ∀ j, ∃ μ : K, A *ᵥ b j = μ • b j := by
    intro j
    have h : b0 (e.symm j) ∈ {w : Fin n → K | ∃ μ : K, A *ᵥ w = μ • w} :=
      Module.Basis.ofSpan_subset hspan ⟨e.symm j, rfl⟩
    simpa [b, Module.Basis.reindex_apply] using h
  choose u hu using hb
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix b, b.toMatrix (Pi.basisFun K (Fin n)), u, ?_, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (hu j) i
    simpa [Matrix.mul_apply, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct,
      mul_comm] using h

end Basis

section Torus

variable {K : Type*} [Field K] {n : ℕ}

theorem conj_diagonal_mul (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1)
    (a b : Fin n → K) :
    (P * diagonal a * Q) * (P * diagonal b * Q) = P * diagonal (fun j => a j * b j) * Q := by
  calc (P * diagonal a * Q) * (P * diagonal b * Q)
      = P * diagonal a * (Q * P) * diagonal b * Q := by simp only [Matrix.mul_assoc]
    _ = P * (diagonal a * diagonal b) * Q := by
        rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc P]
    _ = P * diagonal (fun j => a j * b j) * Q := by rw [diagonal_mul_diagonal]

theorem entries_eq_of_conj_eq_scalar (P Q : Matrix (Fin n) (Fin n) K) (hQP : Q * P = 1)
    (a : Fin n → K) (c : K) (h : P * diagonal a * Q = scalar (Fin n) c) (j : Fin n) :
    a j = c := by
  have h1 : diagonal a = scalar (Fin n) c := by
    calc diagonal a = (Q * P) * diagonal a * (Q * P) := by
          rw [hQP, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (P * diagonal a * Q) * P := by simp only [Matrix.mul_assoc]
      _ = Q * scalar (Fin n) c * P := by rw [h]
      _ = scalar (Fin n) c := by
          rw [← (Matrix.scalar_commute c (fun _ => Commute.all _ _) Q).eq, Matrix.mul_assoc, hQP,
            Matrix.mul_one]
  have h2 := congrFun (congrFun h1 j) j
  simpa [Matrix.diagonal_apply_eq, Matrix.scalar_apply] using h2

theorem commute_conj_diagonal (P Q : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (A : Matrix (Fin n) (Fin n) K) (u : Fin n → K)
    (hAP : A * P = P * diagonal u) (a : Fin n → K) :
    (P * diagonal a * Q) * A = A * (P * diagonal a * Q) := by
  have hQA : Q * A = diagonal u * Q := by
    calc Q * A = Q * A * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = Q * (A * P) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * (P * diagonal u) * Q := by rw [hAP]
      _ = (Q * P) * diagonal u * Q := by simp only [Matrix.mul_assoc]
      _ = diagonal u * Q := by rw [hQP, Matrix.one_mul]
  calc (P * diagonal a * Q) * A = P * diagonal a * (Q * A) := by simp only [Matrix.mul_assoc]
    _ = P * (diagonal a * diagonal u) * Q := by rw [hQA]; simp only [Matrix.mul_assoc]
    _ = P * (diagonal u * diagonal a) * Q := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
        simp only [mul_comm]
    _ = (P * diagonal u) * diagonal a * Q := by simp only [Matrix.mul_assoc]
    _ = A * P * diagonal a * Q := by rw [hAP]
    _ = A * (P * diagonal a * Q) := by simp only [Matrix.mul_assoc]


end Torus

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
