module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.LinearAlgebra.Dual.Lemmas

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open Polynomial

theorem poly3_zero {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 2) (a b d : K) (h : ∀ c : K, a * c + b * c ^ q + d * c ^ (q + 1) = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  classical
  let P : K[X] := C a * X + C b * X ^ q + C d * X ^ (q + 1)
  have hP : P = 0 := by
    refine eq_zero_of_forall_eval_zero_of_natDegree_lt_card P (fun r => ?_) ?_
    · simp only [P, eval_add, eval_mul, eval_C, eval_X, eval_pow]
      exact h r
    · have hdeg : P.natDegree ≤ q + 1 := by
        unfold P
        compute_degree!
      have : q + 1 < Cardinal.mk K := by
        rw [Cardinal.mk_fintype, hK]
        have : q + 1 < q ^ 2 := by nlinarith
        exact_mod_cast this
      exact lt_of_le_of_lt (by exact_mod_cast hdeg) this
  have hq1 : 1 ≠ q := by omega
  have hq2 : 1 ≠ q + 1 := by omega
  have hq3 : q ≠ q + 1 := by omega
  have c1 := congrArg (fun p : K[X] => p.coeff 1) hP
  have cq := congrArg (fun p : K[X] => p.coeff q) hP
  have cq1 := congrArg (fun p : K[X] => p.coeff (q + 1)) hP
  have h0 : q ≠ 0 := by omega
  have h0' : q + 1 ≠ 0 := by omega
  simp only [P, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_zero] at c1 cq cq1
  refine ⟨?_, ?_, ?_⟩
  · simpa [hq1, hq2, hq1.symm, hq2.symm, h0, h0'] using c1
  · simpa [hq1, hq2, hq3, hq1.symm, hq2.symm, hq3.symm, h0, h0'] using cq
  · simpa [hq1, hq2, hq3, hq1.symm, hq2.symm, hq3.symm, h0, h0'] using cq1

theorem mem_of_forall_poly {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    {q : ℕ} (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 2) (S : Submodule K V) (σ : K → K)
    (hσ : ∀ c, σ c = c ^ q) (u₁ u₂ u₃ : V)
    (h : ∀ c : K, c • u₁ + σ c • u₂ + (c * σ c) • u₃ ∈ S) :
    u₁ ∈ S ∧ u₂ ∈ S ∧ u₃ ∈ S := by
  have key : ∀ φ : Module.Dual K (V ⧸ S), φ (Submodule.Quotient.mk u₁) = 0 ∧
      φ (Submodule.Quotient.mk u₂) = 0 ∧ φ (Submodule.Quotient.mk u₃) = 0 := by
    intro φ
    refine poly3_zero hq hK _ _ _ fun c => ?_
    have h1 := (Submodule.Quotient.mk_eq_zero S).2 (h c)
    have h2 := congrArg φ h1
    simp only [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, map_add, map_smul,
      smul_eq_mul, map_zero, hσ] at h2
    rw [← h2]
    ring
  refine ⟨?_, ?_, ?_⟩ <;> rw [← Submodule.Quotient.mk_eq_zero,
    ← Module.forall_dual_apply_eq_zero_iff K] <;> intro φ
  · exact (key φ).1
  · exact (key φ).2.1
  · exact (key φ).2.2

theorem poly_finset_zero {K : Type*} [Field K] [Fintype K] (E : Finset ℕ)
    (hE : ∀ e ∈ E, e < Fintype.card K) (a : ℕ → K)
    (h : ∀ c : K, ∑ e ∈ E, a e * c ^ e = 0) : ∀ e ∈ E, a e = 0 := by
  classical
  let P : K[X] := ∑ e ∈ E, C (a e) * X ^ e
  have hP : P = 0 := by
    refine eq_zero_of_forall_eval_zero_of_natDegree_lt_card P (fun r => ?_) ?_
    · simp only [P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
      exact h r
    · have hdeg : P.natDegree ≤ E.sup id := by
        refine natDegree_sum_le_of_forall_le _ _ fun e he => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_X_pow]
        exact Finset.le_sup (f := id) he
      have hlt : E.sup id < Fintype.card K := by
        rw [Finset.sup_lt_iff (by simpa using Fintype.card_pos)]
        exact hE
      have : ((E.sup id : ℕ) : Cardinal) < Cardinal.mk K := by
        rw [Cardinal.mk_fintype]
        exact_mod_cast hlt
      exact lt_of_le_of_lt (by exact_mod_cast hdeg) this
  intro e he
  have := congrArg (fun p : K[X] => p.coeff e) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [Ne.symm hb]) (fun h' => absurd he h')] at this
  simpa using this

theorem mem_of_forall_poly_finset {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] (S : Submodule K V) (E : Finset ℕ) (hE : ∀ e ∈ E, e < Fintype.card K)
    (u : ℕ → V) (h : ∀ c : K, ∑ e ∈ E, c ^ e • u e ∈ S) : ∀ e ∈ E, u e ∈ S := by
  intro e he
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have := poly_finset_zero E hE (fun e => φ (Submodule.mkQ S (u e))) (fun c => by
    have h1 : Submodule.mkQ S (∑ e ∈ E, c ^ e • u e) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).2 (h c)
    have h2 := congrArg φ h1
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _) e he
  exact this

theorem mem_of_forall_poly_inj {K V ι : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Fintype ι] (S : Submodule K V) (ex : ι → ℕ) (hinj : Function.Injective ex)
    (hb : ∀ i, ex i < Fintype.card K) (u : ι → V) (h : ∀ c : K, ∑ i, c ^ ex i • u i ∈ S) :
    ∀ i, u i ∈ S := by
  classical
  intro i0
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  let P : K[X] := ∑ i, C (φ (Submodule.mkQ S (u i))) * X ^ ex i
  have hP : P = 0 := by
    refine eq_zero_of_forall_eval_zero_of_natDegree_lt_card P (fun c => ?_) ?_
    · have h1 : Submodule.mkQ S (∑ i, c ^ ex i • u i) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).2 (h c)
      have h2 := congrArg φ h1
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h2
      simp only [P, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · have hdeg : P.natDegree ≤ Finset.univ.sup ex := by
        refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_X_pow]
        exact Finset.le_sup (f := ex) hi
      have hlt : Finset.univ.sup ex < Fintype.card K := by
        rw [Finset.sup_lt_iff (by simpa using Fintype.card_pos)]
        exact fun i _ => hb i
      have : ((Finset.univ.sup ex : ℕ) : Cardinal) < Cardinal.mk K := by
        rw [Cardinal.mk_fintype]
        exact_mod_cast hlt
      exact lt_of_le_of_lt (by exact_mod_cast hdeg) this
  have := congrArg (fun p : K[X] => p.coeff (ex i0)) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hinj.ne hb.symm])
    (fun h' => absurd (Finset.mem_univ _) h')] at this
  simpa using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
