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

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

section Graph

variable {V : Type*} [CommGroup V] [Finite V]

theorem graph_lemma (hV : ∀ v : V, v ^ 2 = 1) (P A X : Subgroup V) (π : V →* V) (h : MulAut V)
    (hAP : A ≤ P) (hXP : X ≤ P)
    (hπP : ∀ p ∈ P, π p ∈ A) (hπA : ∀ a ∈ A, π a = a)
    (hhP : ∀ p ∈ P, h⁻¹ p ∈ P) (hhπ : ∀ p ∈ P, π (h p) = π p)
    (hhA : ∀ a ∈ A, h a = a)
    (hXA : X ⊓ A = ⊥) (hXsup : ∀ p ∈ P, ∃ x ∈ X, ∃ a ∈ A, p = x * a)
    (hπX : ∀ a ∈ A, ∃ x ∈ X, π x = a)
    (hfix : ∀ l ∈ P, π l = 1 → h l = l → l = 1) :
    ∀ z ∈ A, ∃ x ∈ X, ∃ x' ∈ X, z = x * h x' := by
  classical
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hπh : ∀ p ∈ P, π (h⁻¹ p) = π p := by
    intro p hp
    have := hhπ (h⁻¹ p) (hhP p hp)
    rw [show h (h⁻¹ p) = p from MulAut.apply_inv_self (M := V) h p] at this
    exact this.symm
  let ℓ : V →* V := MonoidHom.id V * π⁻¹
  have hℓ : ∀ p, ℓ p = p * (π p)⁻¹ := fun p => rfl
  have hℓπ : ∀ p ∈ P, π (ℓ p) = 1 := by
    intro p hp
    rw [hℓ, map_mul, map_inv, hπA _ (hπP p hp), mul_inv_cancel]
  have hℓP : ∀ p ∈ P, ℓ p ∈ P := fun p hp => by
    rw [hℓ]; exact mul_mem hp (inv_mem (hAP (hπP p hp)))
  have hinj : ∀ x₁ ∈ X, ∀ x₂ ∈ X, ℓ x₁ = ℓ x₂ → x₁ = x₂ := by
    intro x₁ h₁ x₂ h₂ he
    have he' : x₁ / π x₁ = x₂ / π x₂ := by simpa [hℓ, div_eq_mul_inv] using he
    have h3 : x₁ / x₂ = π x₁ / π x₂ := div_eq_div_iff_div_eq_div.mp he'
    have hA : x₁ / x₂ ∈ A := by
      rw [h3]
      exact div_mem (hπP x₁ (hXP h₁)) (hπP x₂ (hXP h₂))
    have hX' : x₁ / x₂ ∈ X := X.div_mem h₁ h₂
    have : x₁ / x₂ ∈ X ⊓ A := ⟨hX', hA⟩
    rw [hXA, Subgroup.mem_bot] at this
    exact div_eq_one.mp this
  have hsurjX : ∀ l ∈ P, π l = 1 → ∃ x ∈ X, ℓ x = l := by
    intro l hl hπl
    obtain ⟨x, hx, a, ha, hxa⟩ := hXsup l hl
    refine ⟨x, hx, ?_⟩
    have h1 : π l = π x * a := by rw [hxa, map_mul, hπA a ha]
    have h2 : a = (π x)⁻¹ := by
      rw [hπl] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    rw [hℓ, hxa, h2]
  let Φ₀ : V →* V := MonoidHom.id V * (h⁻¹ : MulAut V).toMonoidHom
  have hΦ₀ : ∀ l, Φ₀ l = l * h⁻¹ l := fun l => rfl
  let S := {l : V // l ∈ P ∧ π l = 1}
  have hS : ∀ l : S, Φ₀ (l : V) ∈ P ∧ π (Φ₀ (l : V)) = 1 := by
    intro l
    refine ⟨?_, ?_⟩
    · rw [hΦ₀]; exact mul_mem l.2.1 (hhP _ l.2.1)
    · rw [hΦ₀, map_mul, hπh _ l.2.1, l.2.2, mul_one]
  let Φ : S → S := fun l => ⟨Φ₀ (l : V), hS l⟩
  have : Finite S := Subtype.finite
  have hΦinj : Function.Injective Φ := by
    intro l l' he
    have he' : Φ₀ (l : V) = Φ₀ (l' : V) := congrArg Subtype.val he
    have hm : ((l : V) / (l' : V)) ∈ P := div_mem l.2.1 l'.2.1
    have hmπ : π ((l : V) / (l' : V)) = 1 := by rw [map_div, l.2.2, l'.2.2, div_one]
    have hkey : Φ₀ ((l : V) / (l' : V)) = 1 := by rw [map_div, he', div_self']
    have hfx : h ((l : V) / (l' : V)) = (l : V) / (l' : V) := by
      have h1 : h⁻¹ ((l : V) / (l' : V)) = ((l : V) / (l' : V))⁻¹ := by
        rw [hΦ₀] at hkey
        exact eq_inv_of_mul_eq_one_right hkey
      rw [hinv] at h1
      have := congrArg h h1
      rw [MulAut.apply_inv_self (M := V)] at this
      exact this.symm
    have := hfix _ hm hmπ hfx
    apply Subtype.ext
    exact div_eq_one.mp this
  have hΦsurj : Function.Surjective Φ := Finite.injective_iff_surjective.mp hΦinj
  intro z hz
  obtain ⟨x₀, hx₀, hπx₀⟩ := hπX z hz
  have hℓx₀ : ℓ x₀ ∈ P ∧ π (ℓ x₀) = 1 := ⟨hℓP x₀ (hXP hx₀), hℓπ x₀ (hXP hx₀)⟩
  obtain ⟨l₀, hl₀⟩ := hΦsurj ⟨ℓ x₀, hℓx₀⟩
  have hl₀' : Φ₀ (l₀ : V) = ℓ x₀ := congrArg Subtype.val hl₀
  obtain ⟨x, hx, hxl⟩ := hsurjX l₀ l₀.2.1 l₀.2.2
  have hh₁ : h⁻¹ (l₀ : V) ∈ P := hhP _ l₀.2.1
  have hh₂ : π (h⁻¹ (l₀ : V)) = 1 := by rw [hπh _ l₀.2.1, l₀.2.2]
  obtain ⟨x', hx', hxl'⟩ := hsurjX _ hh₁ hh₂
  have hxx' : x * x' = x₀ := by
    apply hinj _ (mul_mem hx hx') _ hx₀
    rw [map_mul, hxl, hxl', ← hΦ₀, hl₀']
  refine ⟨x, hx, x', hx', ?_⟩
  have hπxx' : π x * π x' = z := by rw [← map_mul, hxx', hπx₀]
  have e1 : x = (l₀ : V) * π x := by
    have : ℓ x = (l₀ : V) := hxl
    rw [hℓ] at this
    rw [← this]; simp
  have e2 : h x' = (l₀ : V) * π x' := by
    have h3 : x' = h⁻¹ (l₀ : V) * π x' := by
      have : ℓ x' = h⁻¹ (l₀ : V) := hxl'
      rw [hℓ] at this
      rw [← this]; simp
    calc h x' = h (h⁻¹ (l₀ : V) * π x') := by rw [← h3]
      _ = (l₀ : V) * π x' := by
        rw [map_mul, MulAut.apply_inv_self (M := V), hhA _ (hπP x' (hXP hx'))]
  rw [e2]
  calc z = π x * π x' := hπxx'.symm
    _ = ((l₀ : V) * (l₀ : V)) * (π x * π x') := by rw [hsq, one_mul]
    _ = ((l₀ : V) * π x) * ((l₀ : V) * π x') := by ac_rfl
    _ = x * ((l₀ : V) * π x') := by rw [← e1]

end Graph

end CFSG.CGT.PushingUpLit.CGT6.TwoThree
