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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

universe u

namespace CFSG.ClassicalInvolution.Q3

open Module

section Adapted

variable {F : Type*} [Field F] {V : Type u} [AddCommGroup V] [Module F V]

theorem bilin_self_apply_eq_zero [Invertible (2 : F)] {β : LinearMap.BilinForm F V}
    (hβ : β.IsSymm) {g : V →ₗ[F] V} (hg2 : ∀ x, g (g x) = -x)
    (hgβ : ∀ x y, β (g x) (g y) = β x y) (x : V) : β x (g x) = 0 := by
  have h1 : β (g x) (g (g x)) = β x (g x) := hgβ x (g x)
  rw [hg2, map_neg, show β (g x) x = β x (g x) from (hβ.eq x (g x)).symm] at h1
  have h2 : (2 : F) * β x (g x) = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left (Invertible.ne_zero 2)

theorem bilin_norm_combo [Invertible (2 : F)] {β : LinearMap.BilinForm F V}
    (hβ : β.IsSymm) {g : V →ₗ[F] V} (hg2 : ∀ x, g (g x) = -x)
    (hgβ : ∀ x y, β (g x) (g y) = β x y) (a b : F) (x : V) :
    β (a • x + b • g x) (a • x + b • g x) = (a ^ 2 + b ^ 2) * β x x := by
  have h1 := bilin_self_apply_eq_zero hβ hg2 hgβ x
  have h2 : β (g x) x = 0 := by rw [← hβ.eq x (g x)] at *; exact h1
  have h3 : β (g x) (g x) = β x x := hgβ x x
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
    h3]
  ring

variable [Invertible (2 : F)]

theorem exists_adapted_family
    (hsq : ∀ c : F, c ≠ 0 → ∃ a b : F, (a ^ 2 + b ^ 2) * c = 1) :
    ∀ (d : ℕ) {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (β : LinearMap.BilinForm F V) (g : V →ₗ[F] V), β.IsSymm → β.Nondegenerate →
      (∀ x, g (g x) = -x) → (∀ x y, β (g x) (g y) = β x y) → finrank F V = 2 * d →
      ∃ e : Fin d → V, (∀ k l, β (e k) (e l) = if k = l then 1 else 0) ∧
        ∀ k l, β (e k) (g (e l)) = 0 := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ β g _ _ _ _ _
    exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0⟩
  | succ d ih =>
    intro V _ _ _ β g hβ hnd hg2 hgβ hdim
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
    obtain ⟨w, hw⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hnd.ne_zero
      (LinearMap.BilinForm.isSymm_iff.mp hβ)
    obtain ⟨a, b, hab⟩ := hsq _ hw
    set e : V := a • w + b • g w with he
    have hee : β e e = 1 := by rw [he, bilin_norm_combo hβ hg2 hgβ]; exact hab
    have hege : β e (g e) = 0 := bilin_self_apply_eq_zero hβ hg2 hgβ e
    have hgee : β (g e) e = 0 := by rw [← hβ.eq e (g e)] ; exact hege
    have hgege : β (g e) (g e) = 1 := by rw [hgβ]; exact hee
    let φ : V →ₗ[F] F × F := LinearMap.prod (β.flip e) (β.flip (g e))
    let Q : Submodule F V := LinearMap.ker φ
    have hmemQ : ∀ x, x ∈ Q ↔ β x e = 0 ∧ β x (g e) = 0 := by
      intro x
      simp [Q, φ, LinearMap.mem_ker]
    have hQg : ∀ x ∈ Q, g x ∈ Q := by
      intro x hx
      obtain ⟨h1, h2⟩ := (hmemQ x).mp hx
      refine (hmemQ _).mpr ⟨?_, ?_⟩
      · have : e = -(g (g e)) := by rw [hg2]; simp
        rw [this, map_neg, hgβ, h2, neg_zero]
      · rw [hgβ]; exact h1
    have hdec : ∀ v : V, v - ((β v e) • e + (β v (g e)) • g e) ∈ Q := by
      intro v
      refine (hmemQ _).mpr ⟨?_, ?_⟩
      · simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul, hee, hgee]
        ring
      · simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul, hege, hgege]
        ring
    have hrange : LinearMap.range φ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨y.1 • e + y.2 • g e, ?_⟩
      simp [φ, hee, hege, hgee, hgege]
    have hQdim : finrank F Q = 2 * d := by
      have h1 := LinearMap.finrank_range_add_finrank_ker φ
      rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self] at h1
      change finrank F (LinearMap.ker φ) = 2 * d
      omega
    have hleft : ∀ x : Q, (∀ y : Q, β x y = 0) → x = 0 := by
      intro x hx
      obtain ⟨h1, h2⟩ := (hmemQ x).mp x.2
      have hall : ∀ v : V, β x v = 0 := by
        intro v
        have hr := hx ⟨_, hdec v⟩
        have hv : v = (v - ((β v e) • e + (β v (g e)) • g e)) +
            ((β v e) • e + (β v (g e)) • g e) := by abel
        calc β x v = β x ((v - ((β v e) • e + (β v (g e)) • g e)) +
              ((β v e) • e + (β v (g e)) • g e)) := by rw [← hv]
          _ = 0 := by
            rw [map_add, show β x (v - ((β v e) • e + (β v (g e)) • g e)) = 0 from hr, map_add,
              map_smul, map_smul, h1, h2]
            simp
      exact Subtype.ext (hnd.1 x hall)
    have hQnd : (β.domRestrict₁₂ Q Q).Nondegenerate := by
      refine ⟨fun x hx => hleft x hx, fun y hy => hleft y fun z => ?_⟩
      have := hy z
      simpa [LinearMap.domRestrict₁₂_apply, hβ.eq y z] using this
    have hQsymm : LinearMap.BilinForm.IsSymm (β.domRestrict₁₂ Q Q) :=
      LinearMap.BilinForm.isSymm_iff.mpr ((LinearMap.BilinForm.isSymm_iff.mp hβ).domRestrict Q)
    obtain ⟨e', he'1, he'2⟩ := ih (β.domRestrict₁₂ Q Q) (g.restrict hQg) hQsymm hQnd
      (fun x => Subtype.ext (hg2 x)) (fun x y => hgβ x y) hQdim
    have hperp : ∀ k, β (e' k : V) e = 0 ∧ β (e' k : V) (g e) = 0 := fun k =>
      (hmemQ _).mp (e' k).2
    have hgperp : ∀ k, β (g (e' k : V)) e = 0 ∧ β (g (e' k : V)) (g e) = 0 := fun k =>
      (hmemQ _).mp (hQg _ (e' k).2)
    refine ⟨Fin.cons e (fun k => (e' k : V)), ?_, ?_⟩
    · intro k l
      refine Fin.cases ?_ (fun k => ?_) k <;> refine Fin.cases ?_ (fun l => ?_) l
      · simp only [Fin.cons_zero, ite_true]
        exact hee
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [ite_eq_right (Fin.succ_ne_zero l).symm]
        exact (hβ.eq e (e' l)).trans (hperp l).1
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [ite_eq_right (Fin.succ_ne_zero k)]
        exact (hperp k).1
      · simp only [Fin.cons_succ, Fin.succ_inj]
        have := he'1 k l
        simpa [LinearMap.domRestrict₁₂_apply] using this
    · intro k l
      refine Fin.cases ?_ (fun k => ?_) k <;> refine Fin.cases ?_ (fun l => ?_) l
      · simp only [Fin.cons_zero]
        exact hege
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (hβ.eq e (g (e' l : V))).trans (hgperp l).1
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (hperp k).2
      · simp only [Fin.cons_succ]
        have := he'2 k l
        simpa [LinearMap.domRestrict₁₂_apply] using this

end Adapted

end CFSG.ClassicalInvolution.Q3
