module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.L5Count

open scoped Classical

variable {F : Type} [Field F]

@[expose] noncomputable def negCount (ε : Fin 5 → F) : ℕ :=
  (Finset.univ.filter fun i => ε i = -1).card

theorem eq_one_or_neg_one {a : F} (ha : a * a = 1) : a = 1 ∨ a = -1 := by
  have h : (a - 1) * (a + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.1 h with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem neg_one_ne_one (h2 : (2 : F) ≠ 0) : (-1 : F) ≠ 1 := by
  intro h
  apply h2
  linear_combination -h

theorem prod_eq_neg_one_pow {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) :
    ∏ i, ε i = (-1) ^ negCount ε := by
  rw [negCount, ← Finset.prod_const, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => ε i = -1)]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => ε i = -1), ε i =
      ∏ _i ∈ Finset.univ.filter (fun i => ε i = -1), (-1 : F) :=
    Finset.prod_congr rfl fun i hi => (Finset.mem_filter.1 hi).2
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => ¬ ε i = -1), ε i = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    rcases eq_one_or_neg_one (hε i) with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.1 hi).2
  rw [h1, h2, mul_one]

theorem even_negCount (h2 : (2 : F) ≠ 0) {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1)
    (hdet : ∏ i, ε i = 1) : Even (negCount ε) := by
  rw [prod_eq_neg_one_pow hε] at hdet
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at hdet
  exact neg_one_ne_one h2 hdet

theorem negCount_le (ε : Fin 5 → F) : negCount ε ≤ 5 := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin 5)) (fun i => ε i = -1)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem eq_one_of_negCount_eq_zero {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1)
    (h0 : negCount ε = 0) : ∀ i, ε i = 1 := by
  intro i
  rcases eq_one_or_neg_one (hε i) with h | h
  · exact h
  · exfalso
    have : i ∈ Finset.univ.filter (fun i => ε i = -1) := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    rw [negCount, Finset.card_eq_zero] at h0
    rw [h0] at this
    exact Finset.notMem_empty _ this

section Group

variable {E : Type} [Group E] [Fintype E]

theorem card_filter_neg_one (h2 : (2 : F) ≠ 0) (φ : E → F) (hmul : ∀ e f, φ (e * f) = φ e * φ f)
    (hsq : ∀ e, φ e * φ e = 1) :
    (Finset.univ.filter fun e => φ e = -1).card = 0 ∨
      2 * (Finset.univ.filter fun e => φ e = -1).card = Fintype.card E := by
  by_cases hne : ∃ e₀, φ e₀ = -1
  · right
    obtain ⟨e₀, he₀⟩ := hne
    have hbij : (Finset.univ.filter fun e => φ e = 1).card =
        (Finset.univ.filter fun e => φ e = -1).card := by
      refine Finset.card_bij (fun e _ => e₀ * e) ?_ ?_ ?_
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmul, he₀, he.2, mul_one]
      · intro e _ f _ h
        exact mul_left_cancel h
      · intro f hf
        rw [Finset.mem_filter] at hf
        refine ⟨e₀⁻¹ * f, ?_, by group⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hφ1 : φ 1 = 1 := by
          have h := hmul 1 1
          rw [mul_one] at h
          exact h.trans (hsq 1)
        have h1 : φ e₀⁻¹ * φ e₀ = 1 := by rw [← hmul, inv_mul_cancel, hφ1]
        rw [hmul, hf.2]
        rw [he₀] at h1
        exact h1
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E))
      (fun e => φ e = -1)
    have hnot : (Finset.univ.filter fun e => ¬ φ e = -1) = Finset.univ.filter fun e => φ e = 1 := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases eq_one_or_neg_one (hsq e) with h | h
      · rw [h]
        exact ⟨fun _ => rfl, fun _ => neg_one_ne_one h2 ∘ Eq.symm⟩
      · rw [h]
        exact ⟨fun h' => absurd rfl h', fun h' => absurd h' (neg_one_ne_one h2)⟩
    rw [hnot, hbij, Finset.card_univ] at hsplit
    omega
  · left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _ h
    exact hne ⟨e, h⟩

theorem exists_negCount_two_four (h2 : (2 : F) ≠ 0) (hE : Fintype.card E = 8) (ε : E → Fin 5 → F)
    (hmul : ∀ e f i, ε (e * f) i = ε e i * ε f i) (hsq : ∀ e i, ε e i * ε e i = 1)
    (hinj : ∀ e, (∀ i, ε e i = 1) → e = 1) (hdet : ∀ e, ∏ i, ε e i = 1) :
    (∃ e, negCount (ε e) = 2) ∧ ∃ e, negCount (ε e) = 4 := by
  have hval : ∀ e, e ≠ 1 → negCount (ε e) = 2 ∨ negCount (ε e) = 4 := by
    intro e he
    have hev := even_negCount h2 (hsq e) (hdet e)
    have hle := negCount_le (ε e)
    have h0 : negCount (ε e) ≠ 0 := fun h0 => he (hinj e (eq_one_of_negCount_eq_zero (hsq e) h0))
    obtain ⟨k, hk⟩ := hev
    omega
  have h1 : negCount (ε 1) = 0 := by
    have hε1 : ∀ i, ε 1 i = 1 := by
      intro i
      have h := hmul 1 1 i
      rw [mul_one] at h
      have h' : ε 1 i * ε 1 i = ε 1 i := h.symm
      rw [hsq 1 i] at h'
      exact h'.symm
    rw [negCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ h
    rw [hε1 i] at h
    exact neg_one_ne_one h2 h.symm
  have hsum : ∑ e, negCount (ε e) =
      ∑ i : Fin 5, (Finset.univ.filter fun e => ε e i = -1).card := by
    simp only [negCount, Finset.card_filter]
    exact Finset.sum_comm
  have hcol : ∀ i : Fin 5, (Finset.univ.filter fun e => ε e i = -1).card = 0 ∨
      (Finset.univ.filter fun e => ε e i = -1).card = 4 := by
    intro i
    rcases card_filter_neg_one h2 (fun e => ε e i) (fun e f => hmul e f i) (fun e => hsq e i) with h | h
    · exact Or.inl h
    · right
      rw [hE] at h
      omega
  have hsum4 : ∃ c ≤ 5, ∑ e, negCount (ε e) = 4 * c := by
    refine ⟨(Finset.univ.filter fun i : Fin 5 =>
      (Finset.univ.filter fun e => ε e i = -1).card = 4).card, ?_, ?_⟩
    · have := Finset.card_filter_le (Finset.univ : Finset (Fin 5))
        (fun i : Fin 5 => (Finset.univ.filter fun e => ε e i = -1).card = 4)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact this
    · rw [hsum, Finset.card_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hcol i with h | h
      · rw [h]
        simp
      · rw [h]
        simp
  obtain ⟨c, hc5, hc⟩ := hsum4
  have hsplit : ∑ e, negCount (ε e) = ∑ e ∈ Finset.univ.erase 1, negCount (ε e) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : E)), h1, zero_add]
  have hcard7 : (Finset.univ.erase (1 : E)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hE]
  refine ⟨?_, ?_⟩
  · by_contra hno
    push Not at hno
    have hall : ∀ e ∈ Finset.univ.erase (1 : E), negCount (ε e) = 4 := by
      intro e he
      rcases hval e (Finset.ne_of_mem_erase he) with h | h
      · exact absurd h (hno e)
      · exact h
    rw [Finset.sum_congr rfl hall, Finset.sum_const, hcard7] at hsplit
    simp only [smul_eq_mul] at hsplit
    omega
  · by_contra hno
    push Not at hno
    have hall : ∀ e ∈ Finset.univ.erase (1 : E), negCount (ε e) = 2 := by
      intro e he
      rcases hval e (Finset.ne_of_mem_erase he) with h | h
      · exact h
      · exact absurd h (hno e)
    rw [Finset.sum_congr rfl hall, Finset.sum_const, hcard7] at hsplit
    simp only [smul_eq_mul] at hsplit
    omega

end Group

end CFSG.GH74.Generic.BProg.B2.T4.L5Count
