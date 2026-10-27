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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

section Clean

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_clean (σ : Perm Ω) (F : Ω → Prop) (hσ1 : ∀ x, F x → σ x ≠ x)
    (hσ2 : ∀ x, F x → σ (σ x) = x) (hFσ : ∀ x, F x → F (σ x)) (Ss : Subgroup (Perm Ω)) (hsw : ∀ x, F x → swap x (σ x) ∈ Ss)
    (g : Perm Ω) (hg : g ∈ Ss) (hgF : ∀ x, F x → g x = x ∨ g x = σ x) :
    ∃ g0 ∈ Ss, (∀ x, F x → g0 x = x) ∧ (∀ x, ¬ F x → g0 x = g x) := by
  classical
  suffices H : ∀ n : ℕ, ∀ g ∈ Ss, (∀ x, F x → g x = x ∨ g x = σ x) →
      (Finset.univ.filter fun x => F x ∧ g x ≠ x).card = n →
      ∃ g0 ∈ Ss, (∀ x, F x → g0 x = x) ∧ (∀ x, ¬ F x → g0 x = g x) from
    H _ g hg hgF rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg hgF hcard
    by_cases h : ∃ x, F x ∧ g x ≠ x
    · obtain ⟨x, hx, hgx⟩ := h
      have hgx' : g x = σ x := (hgF x hx).resolve_left hgx
      have hgσx : g (σ x) = x := by
        rcases hgF (σ x) (hFσ x hx) with e | e
        · exact absurd (g.injective (e.trans hgx'.symm)) (hσ1 x hx)
        · rw [e, hσ2 x hx]
      set g' := g * swap x (σ x) with hg'
      have hg'mem : g' ∈ Ss := Ss.mul_mem hg (hsw x hx)
      have hg'x : g' x = x := by
        simp only [hg', Perm.mul_apply, swap_apply_left, hgσx]
      have hg'σx : g' (σ x) = σ x := by
        simp only [hg', Perm.mul_apply, swap_apply_right, hgx']
      have hg'off : ∀ w, w ≠ x → w ≠ σ x → g' w = g w := by
        intro w h1 h2
        simp only [hg', Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
      have hg'F : ∀ w, F w → g' w = w ∨ g' w = σ w := by
        intro w hw
        by_cases h1 : w = x
        · subst h1; exact Or.inl hg'x
        · by_cases h2 : w = σ x
          · subst h2; exact Or.inl hg'σx
          · rw [hg'off w h1 h2]; exact hgF w hw
      have hlt : (Finset.univ.filter fun w => F w ∧ g' w ≠ w).card < n := by
        rw [← hcard]
        refine Finset.card_lt_card ⟨?_, ?_⟩
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          refine ⟨hw.1, fun e => hw.2 ?_⟩
          by_cases h1 : w = x
          · subst h1; exact hg'x
          · by_cases h2 : w = σ x
            · subst h2; exact hg'σx
            · rw [hg'off w h1 h2]; exact e
        · intro hsub
          have := hsub (show x ∈ (Finset.univ.filter fun w => F w ∧ g w ≠ w) by simp [hx, hgx])
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this.2 hg'x
      obtain ⟨g0, hg0, hg0F, hg0off⟩ := ih _ hlt g' hg'mem hg'F rfl
      refine ⟨g0, hg0, hg0F, fun w hw => ?_⟩
      rw [hg0off w hw]
      exact hg'off w (fun e => hw (e ▸ hx)) (fun e => hw (e ▸ hFσ x hx))
    · push Not at h
      exact ⟨g, hg, h, fun _ _ => rfl⟩

end Clean

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
