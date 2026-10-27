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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalInvolution.Asc77.S4

open Equiv Equiv.Perm

@[expose] def swaps4 : List (Perm (Fin 4)) :=
  [swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3]

@[expose] def perms4 : List (Perm (Fin 4)) :=
  [1] ++ swaps4 ++ (swaps4.flatMap fun x => swaps4.map fun y => x * y) ++
    (swaps4.flatMap fun x => swaps4.flatMap fun y => swaps4.map fun w => x * y * w)

theorem mem_swaps4_of_isSwap {σ : Perm (Fin 4)} (hσ : σ.IsSwap) : σ ∈ swaps4 := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  revert x y
  decide

theorem isSwap_of_mem_swaps4 {σ : Perm (Fin 4)} (hσ : σ ∈ swaps4) : σ.IsSwap := by
  simp only [swaps4, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, by decide, rfl⟩

theorem exists_third_swap : ∀ τ₁ ∈ swaps4, ∀ τ₂ ∈ swaps4, τ₁ ≠ τ₂ → τ₁ * τ₂ = τ₂ * τ₁ →
    ∃ τ₃ ∈ swaps4, τ₁ * τ₃ ≠ τ₃ * τ₁ ∧ τ₂ * τ₃ ≠ τ₃ * τ₂ := by decide

theorem swap_conj : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∃ σ ∈ perms4, σ * a * σ⁻¹ = b := by decide

theorem swap_word : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, a ≠ b → a * b = b * a →
    a * c ≠ c * a → ∀ t ∈ swaps4,
      t = a ∨ t = b ∨ t = c ∨ t = a * c * a ∨ t = b * c * b ∨ t = a * b * c * b * a := by
  decide

theorem swap_triple_conj : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, a ≠ b → a * b = b * a →
    a * c ≠ c * a → ∀ a' ∈ swaps4, ∀ b' ∈ swaps4, ∀ c' ∈ swaps4, a' ≠ b' → a' * b' = b' * a' →
    a' * c' ≠ c' * a' → ∃ σ : Perm (Fin 4), σ * a * σ⁻¹ = a' ∧ σ * b * σ⁻¹ = b' ∧
      σ * c * σ⁻¹ = c' := by
  have h : ∀ a ∈ swaps4, ∀ b ∈ swaps4, ∀ c ∈ swaps4, a ≠ b → a * b = b * a →
      a * c ≠ c * a → ∀ a' ∈ swaps4, ∀ b' ∈ swaps4, ∀ c' ∈ swaps4, a' ≠ b' → a' * b' = b' * a' →
      a' * c' ≠ c' * a' → ∃ σ ∈ perms4, σ * a * σ⁻¹ = a' ∧ σ * b * σ⁻¹ = b' ∧
        σ * c * σ⁻¹ = c' := by decide
  intro a ha b hb c hc hab hcomm hac a' ha' b' hb' c' hc' hab' hcomm' hac'
  obtain ⟨σ, -, hσ⟩ := h a ha b hb c hc hab hcomm hac a' ha' b' hb' c' hc' hab' hcomm' hac'
  exact ⟨σ, hσ⟩

section Transfer

variable {Q : Type*} [Group Q] {Δ : Set Q} {e : Q ≃* Perm (Fin 4)}

theorem mem_swaps4_of_mem (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {x : Q} (hx : x ∈ Δ) :
    e x ∈ swaps4 :=
  mem_swaps4_of_isSwap ((he x).mp hx)

theorem symm_mem_of_mem_swaps4 (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {σ : Perm (Fin 4)}
    (hσ : σ ∈ swaps4) : e.symm σ ∈ Δ := by
  rw [he, MulEquiv.apply_symm_apply]
  exact isSwap_of_mem_swaps4 hσ

theorem exists_third (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a b : Q} (ha : a ∈ Δ) (hb : b ∈ Δ)
    (hab : a ≠ b) (hc : a * b = b * a) :
    ∃ c ∈ Δ, a * c ≠ c * a ∧ b * c ≠ c * b := by
  obtain ⟨τ, hτ, h1, h2⟩ := exists_third_swap (e a) (mem_swaps4_of_mem he ha) (e b)
    (mem_swaps4_of_mem he hb) (fun h => hab (e.injective h)) (by rw [← map_mul, ← map_mul, hc])
  refine ⟨e.symm τ, symm_mem_of_mem_swaps4 he hτ, fun h => h1 ?_, fun h => h2 ?_⟩
  · have := congrArg e h
    simpa using this
  · have := congrArg e h
    simpa using this

theorem exists_frame_conj (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a b c a' b' c' : Q} (ha : a ∈ Δ)
    (hb : b ∈ Δ) (hc : c ∈ Δ) (ha' : a' ∈ Δ) (hb' : b' ∈ Δ) (hc' : c' ∈ Δ) (hab : a ≠ b)
    (hcomm : a * b = b * a) (hac : a * c ≠ c * a) (hab' : a' ≠ b') (hcomm' : a' * b' = b' * a')
    (hac' : a' * c' ≠ c' * a') :
    ∃ y : Q, y * a * y⁻¹ = a' ∧ y * b * y⁻¹ = b' ∧ y * c * y⁻¹ = c' := by
  have h := swap_triple_conj (e a) (mem_swaps4_of_mem he ha) (e b) (mem_swaps4_of_mem he hb) (e c)
    (mem_swaps4_of_mem he hc) (fun h => hab (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac (e.injective (by rw [map_mul, map_mul, h]))) (e a') (mem_swaps4_of_mem he ha')
    (e b') (mem_swaps4_of_mem he hb') (e c') (mem_swaps4_of_mem he hc')
    (fun h => hab' (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm'])
    (fun h => hac' (e.injective (by rw [map_mul, map_mul, h])))
  obtain ⟨σ, h1, h2, h3⟩ := h
  refine ⟨e.symm σ, e.injective ?_, e.injective ?_, e.injective ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem exists_conj_of_mem (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a b : Q} (ha : a ∈ Δ) (hb : b ∈ Δ) :
    ∃ y : Q, y * a * y⁻¹ = b := by
  obtain ⟨σ, -, hσ⟩ := swap_conj (e a) (mem_swaps4_of_mem he ha) (e b) (mem_swaps4_of_mem he hb)
  exact ⟨e.symm σ, e.injective (by simpa using hσ)⟩

theorem mem_closure_frame (he : ∀ x, x ∈ Δ ↔ (e x).IsSwap) {a b c : Q} (ha : a ∈ Δ) (hb : b ∈ Δ)
    (hc : c ∈ Δ) (hab : a ≠ b) (hcomm : a * b = b * a) (hac : a * c ≠ c * a) {x : Q}
    (hx : x ∈ Δ) : x ∈ Subgroup.closure ({a, b, c} : Set Q) := by
  have h := swap_word (e a) (mem_swaps4_of_mem he ha) (e b) (mem_swaps4_of_mem he hb) (e c)
    (mem_swaps4_of_mem he hc) (fun h => hab (e.injective h)) (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hac (e.injective (by rw [map_mul, map_mul, h]))) (e x) (mem_swaps4_of_mem he hx)
  have mA : a ∈ Subgroup.closure ({a, b, c} : Set Q) := Subgroup.subset_closure (by simp)
  have mB : b ∈ Subgroup.closure ({a, b, c} : Set Q) := Subgroup.subset_closure (by simp)
  have mC : c ∈ Subgroup.closure ({a, b, c} : Set Q) := Subgroup.subset_closure (by simp)
  have key : ∀ w : Q, e x = e w → w ∈ Subgroup.closure ({a, b, c} : Set Q) →
      x ∈ Subgroup.closure ({a, b, c} : Set Q) := fun w hw hmem => by
    rwa [e.injective hw]
  rcases h with h | h | h | h | h | h
  · exact key a h mA
  · exact key b h mB
  · exact key c h mC
  · exact key (a * c * a) (by rw [h, map_mul, map_mul])
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ mA mC) mA)
  · exact key (b * c * b) (by rw [h, map_mul, map_mul])
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ mB mC) mB)
  · exact key (a * b * c * b * a) (by rw [h, map_mul, map_mul, map_mul, map_mul])
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ mA mB) mC) mB) mA)

end Transfer

end CFSG.ClassicalInvolution.Asc77.S4
