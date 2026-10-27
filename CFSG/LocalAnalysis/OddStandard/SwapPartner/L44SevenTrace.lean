module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44SevenFixed
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Matrix

variable {K : Type*} [Field K]

theorem trace_mul_self_of_charTwo [CharP K 2] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) : trace (M * M) = trace M ^ 2 := by
  classical
  have hsq : trace M ^ 2 = ∑ i, (M i i) ^ 2 := by
    have h : trace M = ∑ i, M i i := by simp [Matrix.trace]
    rw [h, sum_pow_char]
  have hmul : trace (M * M) = ∑ i, ∑ j, M i j * M j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have hoff : (∑ p ∈ (Finset.univ : Finset n).offDiag, M p.1 p.2 * M p.2 p.1) = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p hp
      have h : M p.2 p.1 * M p.1 p.2 = M p.1 p.2 * M p.2 p.1 := mul_comm _ _
      rw [h]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      exact (Finset.mem_offDiag.mp hp).2.2 (Prod.ext_iff.mp h).2
    · intro p hp
      rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    · intro p hp
      rfl
  have hdiag : (∑ p ∈ (Finset.univ : Finset n).diag, M p.1 p.2 * M p.2 p.1)
      = ∑ i, M i i * M i i := by
    simp [Finset.sum_diag]
  have huniv : (Finset.univ : Finset n).diag ∪ (Finset.univ : Finset n).offDiag
      = (Finset.univ : Finset (n × n)) := by
    rw [Finset.diag_union_offDiag]
    ext p
    simp
  have hmain : (∑ p : n × n, M p.1 p.2 * M p.2 p.1) = ∑ i, M i i * M i i := by
    rw [← huniv, Finset.sum_union (Finset.disjoint_diag_offDiag (Finset.univ : Finset n))]
    rw [hdiag, hoff, add_zero]
  have hprod : (∑ i, ∑ j, M i j * M j i) = ∑ p : n × n, M p.1 p.2 * M p.2 p.1 :=
    (Fintype.sum_prod_type' (f := fun i j => M i j * M j i)).symm
  calc trace (M * M) = ∑ i, M i i * M i i := by rw [hmul, hprod, hmain]
    _ = trace M ^ 2 := by
      rw [hsq]
      simp [sq]

theorem trace_of_pow_seven (hK : Nat.card K = 4) {g : Matrix (Fin 4) (Fin 4) K}
    (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) :
    (trace g = 0 ∨ trace g = 1) ∧ trace (g ^ 6) = trace g + 1 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hcardK]; norm_num)
  have h4 : ((4 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_mod (R := K) (p := 2) 4, show (4 % 2 : ℕ) = 0 by norm_num,
      Nat.cast_zero]
  have h7 : ((7 : ℕ) : K) = 1 := by
    rw [CharP.cast_eq_mod (R := K) (p := 2) 7, show (7 % 2 : ℕ) = 1 by norm_num,
      Nat.cast_one]
  have hpow4 : ∀ x : K, x ^ 4 = x := by
    intro x
    have h := FiniteField.pow_card x
    rwa [hcardK] at h
  let t : ℕ → K := fun j => trace (g ^ j)
  have ht : ∀ j, t (2 * j) = t j ^ 2 := by
    intro j
    have h : g ^ j * g ^ j = g ^ (2 * j) := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm]
    have hh := trace_mul_self_of_charTwo (K := K) (M := g ^ j)
    rw [h] at hh
    exact hh
  have hg8 : g ^ 8 = g := by
    rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, hg7, one_mul, pow_one]
  have hg10 : g ^ 10 = g ^ 3 := by
    rw [show (10 : ℕ) = 3 + 7 by norm_num, pow_add, hg7, mul_one]
  have hg12 : g ^ 12 = g ^ 5 := by
    rw [show (12 : ℕ) = 5 + 7 by norm_num, pow_add, hg7, mul_one]
  have ht0 : t 0 = 0 := by
    show trace (g ^ 0) = 0
    rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact h4
  have ht4 : t 4 = t 1 := by
    calc t 4 = t 2 ^ 2 := ht 2
      _ = (t 1 ^ 2) ^ 2 := by rw [ht 1]
      _ = t 1 ^ 4 := by rw [← pow_mul]
      _ = t 1 := hpow4 (t 1)
  have ht1 : t 1 = trace g := by
    show trace (g ^ 1) = trace g
    rw [pow_one]
  have ht1sq : t 1 = t 1 ^ 2 := by
    have h18 : t 1 = t 8 := by
      show trace (g ^ 1) = trace (g ^ 8)
      rw [pow_one, hg8]
    calc t 1 = t 8 := h18
      _ = t 4 ^ 2 := ht 4
      _ = t 1 ^ 2 := by rw [ht4]
  have ht1_or : t 1 = 0 ∨ t 1 = 1 := by
    have h : t 1 * (t 1 - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq, ← ht1sq, sub_self]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have ht2 : t 2 = t 1 := by rw [ht 1, ← ht1sq]
  have ht6 : t 6 = t 3 ^ 2 := ht 3
  have ht5 : t 5 = t 3 := by
    have h512 : t 5 = t 12 := by
      show trace (g ^ 5) = trace (g ^ 12)
      rw [hg12]
    calc t 5 = t 12 := h512
      _ = t 6 ^ 2 := ht 6
      _ = (t 3 ^ 2) ^ 2 := by rw [ht6]
      _ = t 3 ^ 4 := by rw [← pow_mul]
      _ = t 3 := hpow4 (t 3)
  have ht3sq : t 3 = t 3 ^ 2 := by
    have h310 : t 3 = t 10 := by
      show trace (g ^ 3) = trace (g ^ 10)
      rw [hg10]
    calc t 3 = t 10 := h310
      _ = t 5 ^ 2 := ht 5
      _ = t 3 ^ 2 := by rw [ht5]
  have ht6' : t 6 = t 3 := by rw [ht6, ← ht3sq]
  set N : Matrix (Fin 4) (Fin 4) K := ∑ j ∈ Finset.range 7, g ^ j with hNdef
  have hgN : g * N = N := by
    have hNexpand : N = (∑ j ∈ Finset.range 6, g ^ (j + 1)) + 1 := by
      rw [hNdef, Finset.sum_range_succ']
      simp
    calc g * N = g * (∑ j ∈ Finset.range 7, g ^ j) := by rw [hNdef]
      _ = ∑ j ∈ Finset.range 7, g * g ^ j := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range 7, g ^ (j + 1) := by simp_rw [pow_succ']
      _ = (∑ j ∈ Finset.range 6, g ^ (j + 1)) + g ^ 7 := by rw [Finset.sum_range_succ]
      _ = (∑ j ∈ Finset.range 6, g ^ (j + 1)) + 1 := by rw [hg7]
      _ = N := hNexpand.symm
  have hNN : N * N = N := by
    have hgNj : ∀ j, g ^ j * N = N := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_assoc, hgN, ih]
    calc N * N = (∑ j ∈ Finset.range 7, g ^ j) * N := by rw [hNdef]
      _ = ∑ j ∈ Finset.range 7, g ^ j * N := by rw [Finset.sum_mul]
      _ = ∑ j ∈ Finset.range 7, N := by simp_rw [hgNj]
      _ = (Finset.range 7).card • N := by rw [Finset.sum_const]
      _ = 7 • N := by rw [Finset.card_range]
      _ = N := by rw [← Nat.cast_smul_eq_nsmul K 7 N, h7, one_smul]
  have hrange_mem : ∀ v : Fin 4 → K,
      v ∈ LinearMap.range (Matrix.toLin' N) ↔ g *ᵥ v = v := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec w g N, hgN]
    · intro hv
      refine ⟨v, ?_⟩
      rw [Matrix.toLin'_apply]
      have hgj : ∀ j, g ^ j *ᵥ v = v := by
        intro j
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ', ← Matrix.mulVec_mulVec v g (g ^ j), ih, hv]
      calc N *ᵥ v = (∑ j ∈ Finset.range 7, g ^ j) *ᵥ v := by rw [hNdef]
        _ = ∑ j ∈ Finset.range 7, g ^ j *ᵥ v := by rw [Matrix.sum_mulVec]
        _ = ∑ j ∈ Finset.range 7, v := by simp_rw [hgj]
        _ = 7 • v := by rw [Finset.sum_const, Finset.card_range]
        _ = v := by rw [← Nat.cast_smul_eq_nsmul K 7 v, h7, one_smul]
  have hcard_range : Nat.card (LinearMap.range (Matrix.toLin' N)) = 4 := by
    conv_rhs => rw [← card_fixedVec_eq_four_of_pow_seven hK hg7 hg1]
    exact Nat.card_congr (Equiv.subtypeEquivRight hrange_mem)
  have hfinrank : Module.finrank K (LinearMap.range (Matrix.toLin' N)) = 1 := by
    have hpow := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range (Matrix.toLin' N))
    rw [hcard_range, hK] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) (hpow.symm.trans (pow_one 4).symm)
  have hIdemLin : IsIdempotentElem (Matrix.toLin' N) := by
    show Matrix.toLin' N * Matrix.toLin' N = Matrix.toLin' N
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hNN]
  have htraceN : trace N = 1 := by
    have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' N)) (Matrix.toLin' N) :=
      (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' N)).mpr hIdemLin
    have h1 := hproj.trace
    rw [Matrix.trace_toLin'_eq N, hfinrank] at h1
    simpa using h1
  have htrace_sum : trace N = ∑ j ∈ Finset.range 7, t j := by
    rw [hNdef, Matrix.trace_sum]
  have hsum : ∑ j ∈ Finset.range 7, t j = t 1 + t 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [ht0, ht2, ht4, ht5, ht6']
    calc 0 + 0 + t 1 + t 1 + t 3 + t 1 + t 3 + t 3
        = (t 1 + t 1) + (t 3 + t 3) + (t 1 + t 3) := by ring
      _ = 0 + 0 + (t 1 + t 3) := by
        rw [CharTwo.add_self_eq_zero (t 1), CharTwo.add_self_eq_zero (t 3)]
      _ = t 1 + t 3 := by ring
  have htrace13 : t 1 + t 3 = 1 := by
    rw [← hsum, ← htrace_sum]
    exact htraceN
  have ht31 : t 3 = t 1 + 1 := by
    calc t 3 = 0 + t 3 := (zero_add _).symm
      _ = (t 1 + t 1) + t 3 := by rw [CharTwo.add_self_eq_zero (t 1)]
      _ = t 1 + (t 1 + t 3) := by ring
      _ = t 1 + 1 := by rw [htrace13]
  constructor
  · rw [← ht1]
    exact ht1_or
  · calc trace (g ^ 6) = t 6 := rfl
      _ = t 3 := ht6'
      _ = t 1 + 1 := ht31
      _ = trace g + 1 := by rw [ht1]

end CFSG.OddStandard.AltStdSec.SwapPartner
