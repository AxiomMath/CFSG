module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.AGLEmbedding.ChevOuterD48

theorem mem_of_cyclic_nine {A : Type*} [Group A] [Finite A] [IsCyclic A] (hA : Nat.card A = 9)
    {σ : A} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {H : Subgroup A} (hH : H ≠ ⊥) : σ ∈ H := by
  classical
  have : Fintype A := Fintype.ofFinite A
  obtain ⟨δ, hδ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH
  have hd1 : (δ : A) ≠ 1 := fun h => hδ1 (Subtype.ext h)
  have hdvd : orderOf (δ : A) ∣ 3 ^ 2 := by
    have := orderOf_dvd_natCard (δ : A)
    rwa [hA] at this
  have hne1 : orderOf (δ : A) ≠ 1 := fun h => hd1 (orderOf_eq_one_iff.1 h)
  have h3 : 3 ∣ orderOf (δ : A) := by
    obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rcases i with _ | i
    · exact absurd (by simpa using hio) hne1
    · rw [hio]; exact dvd_pow_self 3 (by omega)
  have hpos : 0 < orderOf (δ : A) := orderOf_pos _
  set τ : A := (δ : A) ^ (orderOf (δ : A) / 3) with hτdef
  have hτH : τ ∈ H := H.pow_mem δ.2 _
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← pow_mul, Nat.div_mul_cancel h3]
    exact pow_orderOf_eq_one _
  have hτ1 : τ ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    have : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ3
    simpa [h] using this
  have hτ12 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel this
  have hcard : (Finset.univ.filter fun a : A => a ^ 3 = 1).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hS : ({1, τ, τ ^ 2} : Finset A) ⊆ Finset.univ.filter fun a : A => a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hτ3
    · rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  have hScard : ({1, τ, τ ^ 2} : Finset A).card = 3 :=
    Finset.card_eq_three.2 ⟨1, τ, τ ^ 2, fun h => hτ1 h.symm, fun h => hτ2 h.symm, hτ12, rfl⟩
  have hSeq := Finset.eq_of_subset_of_card_le hS (by rw [hScard]; exact hcard)
  have hσT : σ ∈ ({1, τ, τ ^ 2} : Finset A) := by
    rw [hSeq]; simp [hσ3]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσT
  rcases hσT with h | h | h
  · exact absurd h hσ1
  · rw [h]; exact hτH
  · rw [h]; exact H.pow_mem hτH 2

theorem exists_phi_mem {X C A : Type*} [Group X] [Group C] [Group A] [Finite A] [IsCyclic A]
    (hA : Nat.card A = 9) (ρ : X →* MulAut C) (fa : A →* MulAut C) (Θ : MulAut C →* A)
    (hΘ : ∀ (g : C) (δ : A), Θ (MulAut.conj g * fa δ) = δ)
    (hex : ∀ α : MulAut C, ∃ (g : C) (δ : A), α = MulAut.conj g * fa δ)
    (hinner : ∀ g : C, ∃ κ : X, ρ κ = MulAut.conj g)
    (hne : ∃ x : X, ∀ g : C, ρ x ≠ MulAut.conj g) {σ : A} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ x : X, ρ x = fa σ := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, δ, hgδ⟩ := hex (ρ x)
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    exact hx g (by rw [hgδ, map_one, mul_one])
  have hmem : δ ∈ (Θ.comp ρ).range := ⟨x, by simp [hgδ, hΘ]⟩
  have hH : (Θ.comp ρ).range ≠ ⊥ := fun h => hδ1 (by
    have := hmem
    rw [h] at this
    simpa using this)
  obtain ⟨y, hy⟩ := mem_of_cyclic_nine hA hσ3 hσ1 hH
  obtain ⟨g', δ', hgδ'⟩ := hex (ρ y)
  have hδσ : δ' = σ := by
    have h1 : Θ (ρ y) = σ := hy
    rw [hgδ', hΘ] at h1
    exact h1
  obtain ⟨κ, hκ⟩ := hinner g'⁻¹
  refine ⟨κ * y, ?_⟩
  rw [map_mul, hκ, hgδ', hδσ, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.AGLEmbedding.ChevOuterD48
