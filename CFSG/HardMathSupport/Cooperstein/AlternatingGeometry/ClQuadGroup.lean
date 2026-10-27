module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness
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

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem fin4_aux : ∀ g : Perm (Fin 4),
    (∃ x y z : Fin 4, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ g x = y ∧ g y = z ∧ g z = x) ∨
    (g = 1 ∨ g = swap 0 1 * swap 2 3 ∨ g = swap 0 2 * swap 1 3 ∨ g = swap 0 3 * swap 1 2) ∨
    ∃ v : Perm (Fin 4),
      (v = 1 ∨ v = swap 0 1 * swap 2 3 ∨ v = swap 0 2 * swap 1 3 ∨ v = swap 0 3 * swap 1 2) ∧
      ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (g * v) x = y ∧ (g * v) y = x ∧ (g * v) z = z := by
  decide

section Transport

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem swap_frame {e : Fin 4 → Ω} (he : Function.Injective e) (x y i : Fin 4) :
    swap (e x) (e y) (e i) = e (swap x y i) := by
  by_cases hix : i = x
  · subst hix; rw [swap_apply_left, swap_apply_left]
  · by_cases hiy : i = y
    · subst hiy; rw [swap_apply_right, swap_apply_right]
    · rw [swap_apply_of_ne_of_ne hix hiy, swap_apply_of_ne_of_ne (fun h => hix (he h))
        (fun h => hiy (he h))]

omit [Fintype Ω] in
theorem swapProd_frame {e : Fin 4 → Ω} (he : Function.Injective e) (a b c d i : Fin 4) :
    (swap (e a) (e b) * swap (e c) (e d)) (e i) = e ((swap a b * swap c d : Perm (Fin 4)) i) := by
  simp only [Perm.mul_apply, swap_frame he]

omit [Fintype Ω] in
theorem swapProd_off {e : Fin 4 → Ω} (a b c d : Fin 4) {i : Ω} (hi : i ∉ Set.range e) :
    (swap (e a) (e b) * swap (e c) (e d)) i = i := by
  simp only [Perm.mul_apply]
  rw [swap_apply_of_ne_of_ne (fun h => hi ⟨c, h.symm⟩) (fun h => hi ⟨d, h.symm⟩),
    swap_apply_of_ne_of_ne (fun h => hi ⟨a, h.symm⟩) (fun h => hi ⟨b, h.symm⟩)]

omit [Fintype Ω] in
theorem eq_of_frame {e : Fin 4 → Ω} {p q : Perm Ω}
    (hp : ∀ i, i ∉ Set.range e → p i = i) (hq : ∀ i, i ∉ Set.range e → q i = i)
    (h : ∀ i, p (e i) = q (e i)) : p = q := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hx
    exact h i
  · rw [hp x hx, hq x hx]

theorem quad_dichotomy {e : Fin 4 → Ω} (he : Function.Injective e) {P : Subgroup (Perm Ω)}
    (hP2 : IsPGroup 2 P) (hsupp : ∀ p ∈ P, ∀ i, i ∉ Set.range e → p i = i)
    (h1 : swap (e 0) (e 1) * swap (e 2) (e 3) ∈ P) (h2 : swap (e 0) (e 2) * swap (e 1) (e 3) ∈ P)
    (h3 : swap (e 0) (e 3) * swap (e 1) (e 2) ∈ P) :
    (∀ p ∈ P, p = 1 ∨ p = swap (e 0) (e 1) * swap (e 2) (e 3) ∨
      p = swap (e 0) (e 2) * swap (e 1) (e 3) ∨ p = swap (e 0) (e 3) * swap (e 1) (e 2)) ∨
    ∃ p ∈ P, ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ p (e x) = e y ∧ p (e y) = e x ∧
      p (e z) = e z := by
  classical
  have hfix : ∀ (p : Perm Ω) , (∀ i, i ∉ Set.range e → p i = i) → ∀ i, ∃ j, p (e i) = e j := by
    intro p hp i
    by_cases hmem : p (e i) ∈ Set.range e
    · obtain ⟨j, hj⟩ := hmem
      exact ⟨j, hj.symm⟩
    · exfalso
      have := hp _ hmem
      exact hmem ⟨i, (p.injective this).symm⟩
  have hframe : ∀ p : Perm Ω, (∀ i, i ∉ Set.range e → p i = i) →
      ∃ g : Perm (Fin 4), ∀ i, p (e i) = e (g i) := by
    intro p hp
    choose g hg using hfix p hp
    have hinj : Function.Injective g := fun i j hij => by
      have : p (e i) = p (e j) := by rw [hg i, hg j, hij]
      exact he (p.injective this)
    exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hinj), fun i => hg i⟩
  have vf1 : ∀ i, (swap (e 0) (e 1) * swap (e 2) (e 3)) (e i) = e ((swap 0 1 * swap 2 3 : Perm (Fin 4)) i) := by
    intro i; simp only [Perm.mul_apply, swap_frame he]
  have vf2 : ∀ i, (swap (e 0) (e 2) * swap (e 1) (e 3)) (e i) = e ((swap 0 2 * swap 1 3 : Perm (Fin 4)) i) := by
    intro i; simp only [Perm.mul_apply, swap_frame he]
  have vf3 : ∀ i, (swap (e 0) (e 3) * swap (e 1) (e 2)) (e i) = e ((swap 0 3 * swap 1 2 : Perm (Fin 4)) i) := by
    intro i; simp only [Perm.mul_apply, swap_frame he]
  have vsupp : ∀ (x y z w : Fin 4) (i : Ω), i ∉ Set.range e →
      (swap (e x) (e y) * swap (e z) (e w)) i = i := by
    intro x y z w i hi
    simp only [Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne (fun h => hi ⟨z, h.symm⟩) (fun h => hi ⟨w, h.symm⟩),
      swap_apply_of_ne_of_ne (fun h => hi ⟨x, h.symm⟩) (fun h => hi ⟨y, h.symm⟩)]
  by_cases hall : ∀ p ∈ P, p = 1 ∨ p = swap (e 0) (e 1) * swap (e 2) (e 3) ∨
      p = swap (e 0) (e 2) * swap (e 1) (e 3) ∨ p = swap (e 0) (e 3) * swap (e 1) (e 2)
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨p, hpP, hp1, hp2, hp3, hp4⟩ := hall
  obtain ⟨g, hg⟩ := hframe p (hsupp p hpP)
  rcases fin4_aux g with ⟨x, y, z, hxy, hyz, hzx, h1', h2', h3'⟩ | hV | ⟨v, hv, x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
  · exfalso
    refine not_isPGroup_of_threeCycle hP2 hpP (a := e x) (b := e y) (c := e z)
      (fun h => hxy (he h)) (fun h => hyz (he h)) (fun h => hzx (he h)) ?_ ?_ ?_
    · rw [hg, h1']
    · rw [hg, h2']
    · rw [hg, h3']
  · exfalso
    rcases hV with rfl | rfl | rfl | rfl
    · exact hp1 (eq_of_frame (hsupp p hpP) (fun i _ => rfl) (fun i => by rw [hg]; rfl))
    · exact hp2 (eq_of_frame (hsupp p hpP) (vsupp 0 1 2 3) (fun i => by rw [hg, vf1]))
    · exact hp3 (eq_of_frame (hsupp p hpP) (vsupp 0 2 1 3) (fun i => by rw [hg, vf2]))
    · exact hp4 (eq_of_frame (hsupp p hpP) (vsupp 0 3 1 2) (fun i => by rw [hg, vf3]))
  ·
    have key : ∀ q : Perm Ω, q ∈ P → (∀ i, i ∉ Set.range e → q i = i) → ∀ (v : Perm (Fin 4)),
        (∀ i, q (e i) = e (v i)) →
        ∀ x y z : Fin 4, x ≠ y → x ≠ z → y ≠ z → (g * v) x = y → (g * v) y = x → (g * v) z = z →
        ∃ p' ∈ P, ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ p' (e x) = e y ∧ p' (e y) = e x ∧
          p' (e z) = e z := by
      intro q hqP hqs v hqv x y z hxy hxz hyz hx hy hz
      refine ⟨p * q, P.mul_mem hpP hqP, x, y, z, hxy, hxz, hyz, ?_, ?_, ?_⟩
      · rw [Perm.mul_apply, hqv, hg]; exact congrArg e hx
      · rw [Perm.mul_apply, hqv, hg]; exact congrArg e hy
      · rw [Perm.mul_apply, hqv, hg]; exact congrArg e hz
    rcases hv with rfl | rfl | rfl | rfl
    · exact key 1 P.one_mem (fun i _ => rfl) 1 (fun i => rfl) x y z hxy hxz hyz hx hy hz
    · exact key _ h1 (vsupp 0 1 2 3) _ vf1 x y z hxy hxz hyz hx hy hz
    · exact key _ h2 (vsupp 0 2 1 3) _ vf2 x y z hxy hxz hyz hx hy hz
    · exact key _ h3 (vsupp 0 3 1 2) _ vf3 x y z hxy hxz hyz hx hy hz

end Transport

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
