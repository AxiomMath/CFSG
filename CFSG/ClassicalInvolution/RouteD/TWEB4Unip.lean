module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Matrix

variable {K : Type} [Field K]

theorem mul_self_eq_trace_smul (N : Matrix (Fin 2) (Fin 2) K) :
    N * N = N.trace • N - N.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem sq_sub_one_eq_zero {p : ℕ} [Fact p.Prime] [CharP K p] {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A ^ p = 1) : (A - 1) * (A - 1) = 0 := by
  set N : Matrix (Fin 2) (Fin 2) K := A - 1 with hN
  have hAN : A = N + 1 := by rw [hN]; abel
  have hNp : N ^ p = 0 := by
    have h1 : (N + 1) ^ p = N ^ p + 1 ^ p :=
      add_pow_char_of_commute p (Commute.one_right N)
    rw [← hAN, hA, one_pow] at h1
    have : N ^ p = 1 - 1 := by
      calc N ^ p = N ^ p + 1 - 1 := by abel
        _ = 1 - 1 := by rw [← h1]
    rw [this, sub_self]
  have hdet : N.det = 0 := by
    have : N.det ^ p = 0 := by rw [← Matrix.det_pow, hNp, Matrix.det_zero]
    exact pow_eq_zero_iff (Nat.Prime.ne_zero Fact.out) |>.mp this
  have hsq : N * N = N.trace • N := by rw [mul_self_eq_trace_smul, hdet]; simp
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, pow_succ]
  by_cases htr : N.trace = 0
  · rw [hsq, htr, zero_smul]
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
    have h0 : N.trace ^ k • N = 0 := by rw [← hpow, ← hk, hNp]
    have hN0 : N = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd (pow_eq_zero_iff'.mp h).1 htr
      · exact h
    rw [hN0] at hsq
    simp at hsq
    exact htr (by rw [hN0]; simp)

end Matrix

section Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_unipotent_data {p : ℕ} [Fact p.Prime] [CharP K p]
    (F : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q) {A : SL(2, K)}
    (hA1 : A ≠ 1) (hAp : A ^ p = 1) :
    ∃ L : V →ₗ[K] V, (∀ v, F.La A v = v + L v) ∧ (∀ v, (F.La A).symm v = v - L v) ∧
      (∀ v, L v ∈ F.span) ∧
      (∀ v w, polar Q (L v) w + polar Q v (L w) + polar Q (L v) (L w) = 0) ∧
      (∀ v, Q (L v) + polar Q v (L v) = 0) ∧ ∃ v, L v ≠ 0 := by
  have hA' : (A : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
    have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K)) hAp
    simpa using this
  have hsq := sq_sub_one_eq_zero hA'
  let L : V →ₗ[K] V := (F.La A).toLinearMap - LinearMap.id
  have hLv : ∀ v, L v = F.incl (((A : Matrix (Fin 2) (Fin 2) K) - 1) * F.coords v) := by
    intro v
    simp only [L, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [F.La_apply, sub_mul, one_mul]
    abel
  have hL1 : ∀ v, F.La A v = v + L v := fun v => by simp [L]
  have hLL : ∀ v, L (L v) = 0 := by
    intro v
    rw [hLv (L v), hLv v, F.coords_incl, ← mul_assoc, hsq, zero_mul, map_zero]
  have hu : F.La A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := F.La_mem_orthogonalGroup A
  refine ⟨L, hL1, fun v => ?_, fun v => ?_, fun v w => ?_, fun v => ?_, ?_⟩
  · rw [LinearEquiv.symm_apply_eq, hL1, map_sub, hLL v, sub_zero]
    abel
  · rw [hLv v]
    exact LinearMap.mem_range_self _ _
  · have h := polar_map_of_mem hu v w
    rw [hL1 v, hL1 w, polar_add_left, polar_add_right, polar_add_right] at h
    linear_combination h
  · have h := map_of_mem hu v
    rw [hL1 v, QuadraticMap.map_add Q v (L v)] at h
    linear_combination h
  · by_contra hcon
    push Not at hcon
    apply hA1
    apply F.La_injective
    refine LinearEquiv.ext fun v => ?_
    rw [hL1, hcon v, add_zero, map_one]
    rfl

end Frame

end CFSG.ClassicalInvolution.RouteD.TWE.B4
