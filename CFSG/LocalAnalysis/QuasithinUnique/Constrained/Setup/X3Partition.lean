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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.QuasithinUnique.Setup.X3

variable {P : Type*} (O : P → Set P)

structure ClassSystem : Prop where
  self_mem : ∀ x, x ∈ O x
  eq_of_mem : ∀ {x z}, z ∈ O x → O z = O x

variable {O}

open Equiv in
theorem classSystem_orbit {Γ : Type*} [Group Γ] {Q : Type*} (φ : Γ →* Perm Q) :
    ClassSystem (fun x : Q => {z | ∃ g, φ g x = z}) where
  self_mem x := ⟨1, by simp⟩
  eq_of_mem := by
    rintro x z ⟨g, rfl⟩
    ext w
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h * g⁻¹, by simp [map_mul, map_inv, Equiv.Perm.inv_def]⟩

theorem ClassSystem.exists_step (hO : ClassSystem O) {C : Set P} (hC : ∀ x ∈ C, O x ⊆ C)
    (hne : C ≠ Set.univ) :
    ∃ z, z ∉ C ∧ Disjoint C (O z) ∧ ∀ x ∈ C ∪ O z, O x ⊆ C ∪ O z := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ C := by
    by_contra h
    push Not at h
    exact hne (Set.eq_univ_of_forall h)
  have hdisj : Disjoint C (O z) := by
    rw [Set.disjoint_left]
    intro w hwC hwz
    have h1 : O w = O z := hO.eq_of_mem hwz
    have h2 : z ∈ O w := by rw [h1]; exact hO.self_mem z
    exact hz (hC w hwC h2)
  refine ⟨z, hz, hdisj, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hC x hx).trans Set.subset_union_left
  · rw [hO.eq_of_mem hx]
    exact Set.subset_union_right

theorem partition_six_fifteen [Finite P] (hO : ClassSystem O) (hcard : Nat.card P = 21)
    (hsz : ∀ x, (O x).ncard = 6 ∨ (O x).ncard = 10 ∨ (O x).ncard = 12 ∨ (O x).ncard = 15 ∨
      (O x).ncard = 20) :
    ∃ x y, (O x).ncard = 6 ∧ (O y).ncard = 15 ∧ ∀ z, z ∈ O x ∨ z ∈ O y := by
  have hunivcard : (Set.univ : Set P).ncard = 21 := by rw [Set.ncard_univ, hcard]
  have hnonempty : Nonempty P := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hcard
  have hC0 : ∀ x ∈ (∅ : Set P), O x ⊆ ∅ := fun x hx => absurd hx (Set.notMem_empty x)
  obtain ⟨z₁, -, -, hC1⟩ := hO.exists_step hC0 (by
    intro h
    have := congrArg Set.Nonempty h
    exact (Set.empty_ne_univ (α := P)) h)
  have hC1' : ∀ x ∈ (∅ ∪ O z₁ : Set P), O x ⊆ ∅ ∪ O z₁ := hC1
  have hn1 : (∅ ∪ O z₁ : Set P).ncard = (O z₁).ncard := by simp
  have hne1 : (∅ ∪ O z₁ : Set P) ≠ Set.univ := by
    intro h
    rw [h, hunivcard] at hn1
    rcases hsz z₁ with h' | h' | h' | h' | h' <;> omega
  obtain ⟨z₂, hz₂, hd₂, hC2⟩ := hO.exists_step hC1' hne1
  have hn2 : ((∅ ∪ O z₁) ∪ O z₂ : Set P).ncard = (O z₁).ncard + (O z₂).ncard := by
    rw [Set.ncard_union_eq hd₂, hn1]
  by_cases hu2 : ((∅ ∪ O z₁) ∪ O z₂ : Set P) = Set.univ
  · rw [hu2, hunivcard] at hn2
    have h1 := hsz z₁
    have h2 := hsz z₂
    have hcov : ∀ z, z ∈ O z₁ ∨ z ∈ O z₂ := by
      intro z
      have : z ∈ ((∅ ∪ O z₁) ∪ O z₂ : Set P) := by rw [hu2]; trivial
      simpa using this
    rcases h1 with h1 | h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
      first
      | omega
      | exact ⟨z₁, z₂, h1, h2, hcov⟩
      | exact ⟨z₂, z₁, h2, h1, fun z => (hcov z).symm⟩
  ·
    obtain ⟨z₃, hz₃, hd₃, hC3⟩ := hO.exists_step hC2 hu2
    have hn3 : (((∅ ∪ O z₁) ∪ O z₂) ∪ O z₃ : Set P).ncard =
        (O z₁).ncard + (O z₂).ncard + (O z₃).ncard := by
      rw [Set.ncard_union_eq hd₃, hn2]
    by_cases hu3 : (((∅ ∪ O z₁) ∪ O z₂) ∪ O z₃ : Set P) = Set.univ
    · exfalso
      rw [hu3, hunivcard] at hn3
      rcases hsz z₁ with h1 | h1 | h1 | h1 | h1 <;> rcases hsz z₂ with h2 | h2 | h2 | h2 | h2 <;>
        rcases hsz z₃ with h3 | h3 | h3 | h3 | h3 <;> omega
    ·
      obtain ⟨z₄, hz₄, hd₄, -⟩ := hO.exists_step hC3 hu3
      have hn4 : ((((∅ ∪ O z₁) ∪ O z₂) ∪ O z₃) ∪ O z₄ : Set P).ncard =
          (O z₁).ncard + (O z₂).ncard + (O z₃).ncard + (O z₄).ncard := by
        rw [Set.ncard_union_eq hd₄, hn3]
      have hle : ((((∅ ∪ O z₁) ∪ O z₂) ∪ O z₃) ∪ O z₄ : Set P).ncard ≤ 21 := by
        rw [← hunivcard]
        exact Set.ncard_le_ncard (Set.subset_univ _)
      exfalso
      rw [hn4] at hle
      rcases hsz z₁ with h1 | h1 | h1 | h1 | h1 <;> rcases hsz z₂ with h2 | h2 | h2 | h2 | h2 <;>
        rcases hsz z₃ with h3 | h3 | h3 | h3 | h3 <;> rcases hsz z₄ with h4 | h4 | h4 | h4 | h4 <;>
          omega

end CFSG.QuasithinUnique.Setup.X3
