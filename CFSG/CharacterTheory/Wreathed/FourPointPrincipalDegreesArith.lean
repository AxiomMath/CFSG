module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Wreathed.FourPointPrincipalDegrees

open scoped BigOperators ComplexConjugate

theorem twelve_eq_toFinset {ι : Type*} [DecidableEq ι]
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι) :
    ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂} : Finset ι) =
      [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].toFinset := by
  simp

theorem sum_twelve {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] (f : ι → M)
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].Nodup) :
    ∑ χ ∈ ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂} : Finset ι), f χ =
      f a₁ + f a₂ + f a₃ + f a₄ + f a₅ + f a₆ + f a₇ + f a₈ + f a₉ + f a₁₀ + f a₁₁ + f a₁₂ := by
  rw [twelve_eq_toFinset, List.sum_toFinset _ h]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

theorem card_twelve {ι : Type*} [DecidableEq ι] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].Nodup) :
    ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂} : Finset ι).card = 12 := by
  rw [twelve_eq_toFinset, List.toFinset_card_of_nodup h]
  rfl

theorem map_val_twelve {ι α : Type*} [DecidableEq ι] (f : ι → α)
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].Nodup) :
    ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂} : Finset ι).val.map f =
      ↑[f a₁, f a₂, f a₃, f a₄, f a₅, f a₆, f a₇, f a₈, f a₉, f a₁₀, f a₁₁, f a₁₂] := by
  rw [twelve_eq_toFinset, List.toFinset_val, h.dedup, Multiset.map_coe]
  rfl

theorem map_val_eight {ι α : Type*} [DecidableEq ι] (f : ι → α) {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ι}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈].Nodup) :
    ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈} : Finset ι).val.map f =
      ↑[f a₁, f a₂, f a₃, f a₄, f a₅, f a₆, f a₇, f a₈] := by
  have e : ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈} : Finset ι) =
      [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈].toFinset := by
    simp
  rw [e, List.toFinset_val, h.dedup, Multiset.map_coe]
  rfl

theorem nodup_drop_middle {ι : Type*} {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι}
    (h : [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂].Nodup) :
    [a₁, a₂, a₃, a₄, a₉, a₁₀, a₁₁, a₁₂].Nodup :=
  h.sublist (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.cons _ (.cons _
    (.cons _ (List.Sublist.refl _)))))))))

theorem not_real_of_pair {α : Type*} (f f' : α → ℂ) (hpair : ∀ g, f' g = conj (f g))
    (hn : ∃ g, conj (f g) ≠ f g) :
    ¬ (∀ g, conj (f g) = f g) ∧ ¬ (∀ g, conj (f' g) = f' g) := by
  obtain ⟨g, hg⟩ := hn
  refine ⟨fun h => hg (h g), fun h => hg ?_⟩
  have h' := h g
  rw [hpair g, Complex.conj_conj] at h'
  exact h'.symm

theorem filter_twelve {ι : Type*} [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    {a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ : ι} (h₁ : p a₁) (h₂ : p a₂) (h₃ : p a₃)
    (h₄ : p a₄) (h₅ : p a₅) (h₆ : p a₆) (h₇ : ¬ p a₇) (h₈ : ¬ p a₈) (h₉ : ¬ p a₉)
    (h₁₀ : ¬ p a₁₀) (h₁₁ : ¬ p a₁₁) (h₁₂ : ¬ p a₁₂) :
    ({a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂} : Finset ι).filter p =
      {a₁, a₂, a₃, a₄, a₅, a₆} := by
  simp only [Finset.filter_insert, Finset.filter_singleton, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    h₁₀, h₁₁, h₁₂, ↓reduceIte]
  rfl

theorem sum_re_of_real {ι : Type*} (s : Finset ι) (A W D : ι → ℂ)
    (hA : ∀ χ, conj (A χ) = A χ) (hD : ∀ χ, conj (D χ) = D χ)
    (h : ∑ χ ∈ s, A χ * A χ * W χ / D χ = 0) :
    ∑ χ ∈ s, A χ * A χ * ((W χ).re : ℂ) / D χ = 0 := by
  have hc : ∑ χ ∈ s, A χ * A χ * conj (W χ) / D χ = 0 := by
    have h' := congrArg conj h
    rw [map_sum, map_zero] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_div₀, map_mul, map_mul, hA χ, hD χ]
  have h2 : ∑ χ ∈ s, A χ * A χ * (W χ + conj (W χ)) / D χ =
      2 * ∑ χ ∈ s, A χ * A χ * ((W χ).re : ℂ) / D χ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.add_conj]
    push_cast
    ring
  have h3 : ∑ χ ∈ s, A χ * A χ * (W χ + conj (W χ)) / D χ = 0 := by
    have e : ∑ χ ∈ s, A χ * A χ * (W χ + conj (W χ)) / D χ =
        ∑ χ ∈ s, A χ * A χ * W χ / D χ + ∑ χ ∈ s, A χ * A χ * conj (W χ) / D χ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [e, h, hc, add_zero]
  rw [h2] at h3
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

theorem sign_sq {p : ℤ} (hp : p = 1 ∨ p = -1) : (p : ℂ) ^ 2 = 1 := by
  rcases hp with rfl | rfl <;> norm_num

theorem first_equation {ι : Type*} [DecidableEq ι] (A W D : ι → ℂ) (d : ι → ℕ)
    {p₀ β κ lam γ ψ η η' ξκ ξκ' ξl ξl' : ι} {pβ pκ pl δ ε ζ : ℤ}
    (hpβ : pβ = 1 ∨ pβ = -1) (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1)
    (hnd : [p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'].Nodup)
    (hA : ∀ χ, conj (A χ) = A χ) (hD : ∀ χ, D χ = d χ)
    (h : ∑ χ ∈ ({p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset ι),
      A χ * A χ * W χ / D χ = 0)
    (A₀ : A p₀ = 1) (Aβ : A β = 3 * pβ) (Aκ : A κ = pκ) (Al : A lam = -5 * pl)
    (Aγ : A γ = -2 * δ) (Aψ : A ψ = -2 * ζ) (Aη : A η = -4 * ε) (Aη' : A η' = -4 * ε)
    (Aξκ : A ξκ = -3 * pκ) (Aξκ' : A ξκ' = -3 * pκ) (Aξl : A ξl = -pl) (Aξl' : A ξl' = -pl)
    (P₀ : (W p₀).re = 1) (Pβ : (W β).re = pβ) (Pκ : (W κ).re = pκ) (Pl : (W lam).re = pl)
    (Pγ : (W γ).re = 0) (Pψ : (W ψ).re = 0) (Pη : (W η).re = 0) (Pη' : (W η').re = 0)
    (Pξκ : (W ξκ).re = 0) (Pξκ' : (W ξκ').re = 0) (Pξl : (W ξl).re = 0)
    (Pξl' : (W ξl').re = 0) (d₀ : d p₀ = 1) :
    (1 : ℂ) + 9 * pβ / d β + pκ / d κ + 25 * pl / d lam = 0 := by
  have hDr : ∀ χ, conj (D χ) = D χ := fun χ => by rw [hD χ, map_natCast]
  have h1 := sum_re_of_real _ A W D hA hDr h
  rw [sum_twelve _ hnd] at h1
  simp only [hD] at h1
  rw [A₀, Aβ, Aκ, Al, Aγ, Aψ, Aη, Aη', Aξκ, Aξκ', Aξl, Aξl', P₀, Pβ, Pκ, Pl, Pγ, Pψ, Pη, Pη',
    Pξκ, Pξκ', Pξl, Pξl', d₀] at h1
  push_cast at h1
  linear_combination h1 - (9 * pβ / d β : ℂ) * sign_sq hpβ - (pκ / d κ : ℂ) * sign_sq hpκ -
    (25 * pl / d lam : ℂ) * sign_sq hpl

theorem second_equation {ι : Type*} [DecidableEq ι] (A T U D : ι → ℂ) (d : ι → ℕ) (i : ℂ)
    {p₀ β κ lam γ ψ η η' ξκ ξκ' ξl ξl' : ι} {pβ pκ pl δ ε ζ : ℤ}
    (hpβ : pβ = 1 ∨ pβ = -1) (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1)
    (hnd : [p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'].Nodup) (hD : ∀ χ, D χ = d χ)
    (hT : ∑ χ ∈ ({p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset ι),
      A χ * A χ * T χ / D χ = 0)
    (hU : ∑ χ ∈ ({p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset ι),
      A χ * A χ * U χ / D χ = 0)
    (A₀ : A p₀ = 1) (Aβ : A β = 3 * pβ) (Aκ : A κ = pκ) (Al : A lam = -5 * pl)
    (Aγ : A γ = -2 * δ) (Aψ : A ψ = -2 * ζ) (Aη : A η = -4 * ε) (Aη' : A η' = -4 * ε)
    (Aξκ : A ξκ = -3 * pκ) (Aξκ' : A ξκ' = -3 * pκ) (Aξl : A ξl = -pl) (Aξl' : A ξl' = -pl)
    (T₀ : T p₀ = 1) (Tβ : T β = 3 * pβ) (Tκ : T κ = -3 * pκ) (Tl : T lam = -pl)
    (Tγ : T γ = -2 * δ) (Tη : T η = -4 * ε * i) (Tψ : T ψ = 2 * ζ) (Tξκ : T ξκ = pκ - 2 * i)
    (Tξl : T ξl = 3 * pl - 2 * i) (Tη' : T η' = 4 * ε * i) (Tξκ' : T ξκ' = pκ + 2 * i)
    (Tξl' : T ξl' = 3 * pl + 2 * i)
    (U₀ : U p₀ = 1) (Uβ : U β = 0) (Uκ : U κ = 0) (Ul : U lam = -pl) (Uγ : U γ = δ)
    (Uη : U η = -ε * i) (Uψ : U ψ = -ζ) (Uξκ : U ξκ = pκ + i) (Uξl : U ξl = i)
    (Uη' : U η' = ε * i) (Uξκ' : U ξκ' = pκ - i) (Uξl' : U ξl' = -i)
    (d₀ : d p₀ = 1) (dη' : d η' = d η) (dξκ : d ξκ = d κ) (dξκ' : d ξκ' = d κ)
    (dξl : d ξl = d lam) (dξl' : d ξl' = d lam) :
    (1 : ℂ) + 9 * pβ / d β + 17 * pκ / d κ - 23 * pl / d lam = 0 := by
  rw [sum_twelve _ hnd] at hT hU
  simp only [hD] at hT hU
  rw [A₀, Aβ, Aκ, Al, Aγ, Aψ, Aη, Aη', Aξκ, Aξκ', Aξl, Aξl', T₀, Tβ, Tκ, Tl, Tγ, Tη, Tψ, Tξκ,
    Tξl, Tη', Tξκ', Tξl', d₀, dη', dξκ, dξκ', dξl, dξl'] at hT
  rw [A₀, Aβ, Aκ, Al, Aγ, Aψ, Aη, Aη', Aξκ, Aξκ', Aξl, Aξl', U₀, Uβ, Uκ, Ul, Uγ, Uη, Uψ, Uξκ,
    Uξl, Uη', Uξκ', Uξl', d₀, dη', dξκ, dξκ', dξl, dξl'] at hU
  push_cast at hT hU
  linear_combination (1 / 3 : ℂ) * hT + (2 / 3 : ℂ) * hU - (9 * pβ / d β : ℂ) * sign_sq hpβ -
    (17 * pκ / d κ : ℂ) * sign_sq hpκ + (23 * pl / d lam : ℂ) * sign_sq hpl

theorem solve_bcl {b c l : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) (h0 : 1 + b + c + l = 0)
    (h1 : b * c * l + 9 * c * l + b * l + 25 * b * c = 0)
    (h2 : b * c * l + 9 * c * l + 17 * b * l - 23 * b * c = 0) :
    b = 27 ∧ c = -7 ∧ l = -21 := by
  have hbl : b * (48 * c - 16 * l) = 0 := by linear_combination h1 - h2
  have hl : l = 3 * c := by
    rcases mul_eq_zero.mp hbl with h | h
    · exact absurd h hb
    · omega
  subst hl
  have hb' : b = -1 - 4 * c := by omega
  subst hb'
  have hq : -4 * (c * ((3 * c + 1) * (c + 7))) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp hq with h | h
  · norm_num at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hc
  rcases mul_eq_zero.mp h with h | h
  · omega
  · omega

theorem sign_mul_eq {p : ℤ} {d : ℕ} {v : ℤ} (hp : p = 1 ∨ p = -1) (h : p * d = v) (hv : 0 < v) :
    p = 1 ∧ (d : ℤ) = v := by
  rcases hp with rfl | rfl <;> omega

theorem sign_mul_eq_neg {p : ℤ} {d : ℕ} {v : ℤ} (hp : p = 1 ∨ p = -1) (h : p * d = v)
    (hv : v < 0) : p = -1 ∧ (d : ℤ) = -v := by
  rcases hp with rfl | rfl <;> omega

theorem signed_degrees_solve {pβ pκ pl : ℤ} {dβ dκ dl : ℕ}
    (hpβ : pβ = 1 ∨ pβ = -1) (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1)
    (hdβ : dβ ≠ 0) (hdκ : dκ ≠ 0) (hdl : dl ≠ 0)
    (h0 : 1 + pβ * dβ + pκ * dκ + pl * dl = 0)
    (h1 : (1 : ℂ) + 9 * pβ / dβ + pκ / dκ + 25 * pl / dl = 0)
    (h2 : (1 : ℂ) + 9 * pβ / dβ + 17 * pκ / dκ - 23 * pl / dl = 0) :
    pβ = 1 ∧ pκ = -1 ∧ pl = -1 ∧ dβ = 27 ∧ dκ = 7 ∧ dl = 21 := by
  have cβ : (dβ : ℂ) ≠ 0 := by exact_mod_cast hdβ
  have cκ : (dκ : ℂ) ≠ 0 := by exact_mod_cast hdκ
  have cl : (dl : ℂ) ≠ 0 := by exact_mod_cast hdl
  have i1 : (((dβ * dκ * dl + 9 * pβ * dκ * dl + pκ * dβ * dl + 25 * pl * dβ * dκ : ℤ)) : ℂ) =
      0 := by
    push_cast
    field_simp at h1
    linear_combination h1
  have i2 : (((dβ * dκ * dl + 9 * pβ * dκ * dl + 17 * pκ * dβ * dl - 23 * pl * dβ * dκ : ℤ)) :
      ℂ) = 0 := by
    push_cast
    field_simp at h2
    linear_combination h2
  have j1 : (dβ * dκ * dl + 9 * pβ * dκ * dl + pκ * dβ * dl + 25 * pl * dβ * dκ : ℤ) = 0 := by
    exact_mod_cast i1
  have j2 : (dβ * dκ * dl + 9 * pβ * dκ * dl + 17 * pκ * dβ * dl - 23 * pl * dβ * dκ : ℤ) = 0 := by
    exact_mod_cast i2
  have sβ : pβ * pβ = 1 := by rcases hpβ with rfl | rfl <;> norm_num
  have sκ : pκ * pκ = 1 := by rcases hpκ with rfl | rfl <;> norm_num
  have sl : pl * pl = 1 := by rcases hpl with rfl | rfl <;> norm_num
  have k1 : (pβ * dβ) * (pκ * dκ) * (pl * dl) + 9 * (pκ * dκ) * (pl * dl) +
      (pβ * dβ) * (pl * dl) + 25 * (pβ * dβ) * (pκ * dκ) = 0 := by
    linear_combination (pβ * pκ * pl) * j1 - (9 * pκ * pl * dκ * dl : ℤ) * sβ -
      (pβ * pl * dβ * dl : ℤ) * sκ - (25 * pβ * pκ * dβ * dκ : ℤ) * sl
  have k2 : (pβ * dβ) * (pκ * dκ) * (pl * dl) + 9 * (pκ * dκ) * (pl * dl) +
      17 * (pβ * dβ) * (pl * dl) - 23 * (pβ * dβ) * (pκ * dκ) = 0 := by
    linear_combination (pβ * pκ * pl) * j2 - (9 * pκ * pl * dκ * dl : ℤ) * sβ -
      (17 * pβ * pl * dβ * dl : ℤ) * sκ + (23 * pβ * pκ * dβ * dκ : ℤ) * sl
  have nβ : pβ * (dβ : ℤ) ≠ 0 := mul_ne_zero (by rcases hpβ with rfl | rfl <;> norm_num)
    (by exact_mod_cast hdβ)
  have nκ : pκ * (dκ : ℤ) ≠ 0 := mul_ne_zero (by rcases hpκ with rfl | rfl <;> norm_num)
    (by exact_mod_cast hdκ)
  obtain ⟨eb, ec, el⟩ := solve_bcl nβ nκ (by linear_combination h0) k1 k2
  obtain ⟨rβ, dβ'⟩ := sign_mul_eq hpβ eb (by norm_num)
  obtain ⟨rκ, dκ'⟩ := sign_mul_eq_neg hpκ ec (by norm_num)
  obtain ⟨rl, dl'⟩ := sign_mul_eq_neg hpl el (by norm_num)
  refine ⟨rβ, rκ, rl, ?_, ?_, ?_⟩ <;> omega

theorem cube_sum {ι : Type*} [DecidableEq ι] (A D : ι → ℂ) (d : ι → ℕ)
    {p₀ β κ lam γ ψ η η' ξκ ξκ' ξl ξl' : ι} {pβ pκ pl δ ε ζ : ℤ}
    (hnd : [p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'].Nodup) (hD : ∀ χ, D χ = d χ)
    (rβ : pβ = 1) (rκ : pκ = -1) (rl : pl = -1) (rδ : δ = 1) (rε : ε = 1) (rζ : ζ = 1)
    (A₀ : A p₀ = 1) (Aβ : A β = 3 * pβ) (Aκ : A κ = pκ) (Al : A lam = -5 * pl)
    (Aγ : A γ = -2 * δ) (Aψ : A ψ = -2 * ζ) (Aη : A η = -4 * ε) (Aη' : A η' = -4 * ε)
    (Aξκ : A ξκ = -3 * pκ) (Aξκ' : A ξκ' = -3 * pκ) (Aξl : A ξl = -pl) (Aξl' : A ξl' = -pl)
    (d₀ : d p₀ = 1) (dβ : d β = 27) (dκ : d κ = 7) (dl : d lam = 21) (dγ : d γ = 6)
    (dψ : d ψ = 14) (dη : d η = 28) (dη' : d η' = 28) (dξκ : d ξκ = 7) (dξκ' : d ξκ' = 7)
    (dξl : d ξl = 21) (dξl' : d ξl' = 21) :
    ∑ χ ∈ ({p₀, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset ι), A χ ^ 3 / D χ =
      64 / 7 := by
  subst rβ rκ rl rδ rε rζ
  rw [sum_twelve _ hnd]
  simp only [hD]
  rw [A₀, Aβ, Aκ, Al, Aγ, Aψ, Aη, Aη', Aξκ, Aξκ', Aξl, Aξl', d₀, dβ, dκ, dl, dγ, dψ, dη, dη', dξκ,
    dξκ', dξl, dξl']
  norm_num

end CFSG.Wreathed.FourPointPrincipalDegrees
