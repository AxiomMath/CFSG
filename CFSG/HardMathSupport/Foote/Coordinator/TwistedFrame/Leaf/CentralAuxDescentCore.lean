module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open Polynomial

section Core

variable {L : Type} [Field L]

@[expose] def Cseq (ε : ℕ → L) (q : ℕ) : ℕ → L
  | 0 => 1
  | j + 1 => ε j * Cseq ε q j ^ q

theorem Cseq_ne_zero {ε : ℕ → L} (hε : ∀ j, ε j ≠ 0) (q : ℕ) : ∀ j, Cseq ε q j ≠ 0
  | 0 => one_ne_zero
  | j + 1 => mul_ne_zero (hε j) (pow_ne_zero _ (Cseq_ne_zero hε q j))

theorem separable_C_mul_X_pow_sub_X {c : L} (hc : c ≠ 0) {n : ℕ} (hn : (n : L) = 0) :
    (C c * X ^ n - X : L[X]).Separable := by
  rw [Polynomial.separable_def]
  have hd : derivative (C c * X ^ n - X : L[X]) = -1 := by
    rw [derivative_sub, derivative_C_mul_X_pow, derivative_X, hn, mul_zero, C_0, zero_mul]
    simp
  rw [hd]
  exact isCoprime_one_right.neg_right

theorem natDegree_C_mul_X_pow_sub_X {c : L} (hc : c ≠ 0) {n : ℕ} (hn : 1 < n) :
    (C c * X ^ n - X : L[X]).natDegree = n := by
  have h1 : (C c * X ^ n : L[X]).natDegree = n := by
    rw [natDegree_C_mul_X_pow n c hc]
  have h2 : (X : L[X]).natDegree = 1 := natDegree_X
  rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [h1, h2]; exact hn), h1]

variable [IsAlgClosed L]

theorem descent_core {V : Type*} [AddCommGroup V] [Module L V] (W : Submodule L V)
    (q : ℕ) (hq : 2 ≤ q) (hq0 : (q : L) = 0) (N : ℕ) (hN : 0 < N) (ε : ℕ → L)
    (hε : ∀ j, ε j ≠ 0) (v : ℕ → V)
    (hW : ∀ a : L, Cseq ε q N * a ^ (q ^ N) = a →
      ∑ j ∈ Finset.range N, (Cseq ε q j * a ^ (q ^ j)) • v j ∈ W) :
    ∀ j < N, v j ∈ W := by
  classical
  intro j₀ hj₀
  by_contra hnot
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hfW' : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    simpa using this
  set P : L[X] := ∑ j ∈ Finset.range N, C (Cseq ε q j * f (v j)) * X ^ (q ^ j) with hP
  have hCN : Cseq ε q N ≠ 0 := Cseq_ne_zero hε q N
  have hqN : (((q ^ N : ℕ)) : L) = 0 := by
    rw [Nat.cast_pow, hq0, zero_pow hN.ne']
  have hqN1 : 1 < q ^ N := Nat.one_lt_pow hN.ne' (by omega)
  set G : L[X] := C (Cseq ε q N) * X ^ (q ^ N) - X with hG
  have hGsep : G.Separable := separable_C_mul_X_pow_sub_X hCN hqN
  have hGdeg : G.natDegree = q ^ N := natDegree_C_mul_X_pow_sub_X hCN hqN1
  have hGne : G ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hGdeg
    omega
  have hcard : G.roots.toFinset.card = q ^ N := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hGsep),
      IsAlgClosed.card_roots_eq_natDegree, hGdeg]
  have hPdeg : P.natDegree < q ^ N := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le (Finset.range N)
      (fun j => C (Cseq ε q j * f (v j)) * X ^ (q ^ j)) (n := q ^ (N - 1)) ?_) ?_
    · intro j hj
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      exact Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.1 hj; omega)
    · calc q ^ (N - 1) < q ^ (N - 1) * q := by
            have : 0 < q ^ (N - 1) := pow_pos (by omega) _
            nlinarith
        _ = q ^ N := by rw [← pow_succ]; congr 1; omega
  have hPzero : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P G.roots.toFinset ?_ (by rw [hcard]; exact hPdeg)
    intro a ha
    have haG : G.eval a = 0 := by
      have := (Multiset.mem_toFinset.1 ha)
      exact ((mem_roots hGne).1 this)
    have haΛ : Cseq ε q N * a ^ (q ^ N) = a := by
      have : Cseq ε q N * a ^ (q ^ N) - a = 0 := by simpa [hG] using haG
      exact sub_eq_zero.1 this
    have hmem := hW a haΛ
    have h0 := hfW' _ hmem
    rw [map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [hP, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcoef : P.coeff (q ^ j₀) = Cseq ε q j₀ * f (v j₀) := by
    simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Nat.pow_right_injective hq h).symm
    · intro h
      exact absurd (Finset.mem_range.2 hj₀) h
  rw [hPzero, coeff_zero] at hcoef
  have := (mul_eq_zero.1 hcoef.symm).resolve_left (Cseq_ne_zero hε q j₀)
  exact hf0 this

end Core

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
