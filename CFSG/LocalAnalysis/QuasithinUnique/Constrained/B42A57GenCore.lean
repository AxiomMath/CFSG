module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
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

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm CFSG.ComponentClassification.PresentationLocal

@[expose] def tab {n : ℕ} (σ : Perm (Fin n)) : List ℕ := (List.finRange n).map fun i => (σ i).val

@[expose] def tmul (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

theorem tab_getD {n : ℕ} (σ : Perm (Fin n)) (i : Fin n) : (tab σ).getD i.val 0 = (σ i).val := by
  unfold tab
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem tab_mul {n : ℕ} (σ τ : Perm (Fin n)) : tab (σ * τ) = tmul (tab σ) (tab τ) := by
  unfold tab tmul
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Perm.mul_apply]
  rw [← tab_getD σ (τ i)]
  rfl

theorem tab_one {n : ℕ} : tab (1 : Perm (Fin n)) = List.range n := by
  unfold tab
  simp

theorem tab_inj {n : ℕ} : Function.Injective (tab (n := n)) := by
  intro σ τ h
  refine Equiv.ext fun i => Fin.ext ?_
  have h1 := tab_getD σ i
  have h2 := tab_getD τ i
  rw [h] at h1
  exact h1.symm.trans h2

structure GenEntry (n : ℕ) where
  T : List (Perm (Fin n))
  Tt : List (List ℕ)
  cs : List (List (Fin n × Fin n))
  ws : List (List ℕ)

namespace GenEntry

variable {n : ℕ} (e : GenEntry n)

@[expose] def swapProd (l : List (Fin n × Fin n)) : Perm (Fin n) :=
  (l.map fun p => swap p.1 p.2).prod

@[expose] def conjugators : List (Perm (Fin n)) := e.cs.map swapProd

@[expose] def gens : List (Perm (Fin n)) :=
  e.conjugators.flatMap fun c => e.T.map fun t => c * t * c⁻¹

@[expose] def evalWord (g : List (Perm (Fin n))) (w : List ℕ) : Perm (Fin n) :=
  (w.map fun i => g.getD i 1).prod

@[expose] def Ok : Prop :=
  e.T.map tab = e.Tt ∧ (∀ l ∈ e.cs, l.length % 2 = 0 ∧ ∀ p ∈ l, p.1 ≠ p.2) ∧
    ∀ k : CarmichaelIndex n, evalWord e.gens (e.ws.getD (k.1.val - 2) []) = carmichaelPerm k

instance : Decidable e.Ok := by
  unfold Ok
  infer_instance

theorem mem_gens {x : Perm (Fin n)} (hx : x ∈ e.gens) :
    x ∈ {y | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, y = c * t * c⁻¹} := by
  unfold gens at hx
  rw [List.mem_flatMap] at hx
  obtain ⟨c, hc, hx⟩ := hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨c, hc, t, ht, rfl⟩

theorem conjugators_mem (he : e.Ok) : ∀ c ∈ e.conjugators, c ∈ alternatingGroup (Fin n) := by
  intro c hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hlen, hne⟩ := he.2.1 l hl
  rw [mem_alternatingGroup]
  unfold swapProd
  have hsw : ∀ g ∈ l.map (fun p => swap p.1 p.2), g.IsSwap := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact ⟨p.1, p.2, hne p hp, rfl⟩
  rw [Perm.sign_prod_list_swap hsw, List.length_map]
  have : Even l.length := Nat.even_iff.2 hlen
  simp [this.neg_one_pow]

theorem alt_le_closure (hn : 3 ≤ n) (he : e.Ok) :
    alternatingGroup (Fin n) ≤
      Subgroup.closure {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹} := by
  set X : Set (Perm (Fin n)) := {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹} with hX
  have hget : ∀ i : ℕ, e.gens.getD i 1 ∈ Subgroup.closure X := by
    intro i
    by_cases hi : i < e.gens.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact Subgroup.subset_closure (e.mem_gens (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (by omega)]
      exact one_mem _
  have hword : ∀ w : List ℕ, evalWord e.gens w ∈ Subgroup.closure X := by
    intro w
    unfold evalWord
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hget i
  have hcarm : ∀ k : CarmichaelIndex n, carmichaelPerm k ∈ Subgroup.closure X := by
    intro k
    rw [← he.2.2 k]
    exact hword _
  have hH : Subgroup.closure (Set.range (carmichaelCycle (n := n))) ≤
      (Subgroup.closure X).comap (alternatingGroup (Fin n)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hcarm k
  rw [closure_range_carmichaelCycle hn] at hH
  intro g hg
  have := hH (Subgroup.mem_top (⟨g, hg⟩ : ↥(alternatingGroup (Fin n))))
  exact this

end GenEntry

end CFSG.QuasithinUnique.B42A57
