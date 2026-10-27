module

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Module
open LinearMap (BilinForm)

namespace Sp6

section Adapted

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_self_of_forall_apply_apply_eq_zero {B : BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {g : V →ₗ[K] V} (hiso : ∀ x y, B (g x) (g y) = B x y)
    (hg3 : ∀ x, g (g (g x)) = x) (hQ : ∀ y, B (g y) y = 0) (u : V) : g u = u := by
  have hinj : ∀ a b, g a = g b → a = b := fun a b h => by
    rw [← hg3 a, ← hg3 b, h]
  have hpol : ∀ u v, B (g u) v + B (g v) u = 0 := by
    intro u v
    have h := hQ (u + v)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hQ u, hQ v] at h
    linear_combination h
  have hsa : ∀ u v, B (g u) v = B u (g v) := by
    intro u v
    have h1 := hpol u v
    have h2 := hB.neg_eq (g v) u
    linear_combination h1 + h2
  have hshift : ∀ u v, B u (g v) = B (g (g u)) v := by
    intro u v
    conv_lhs => rw [← hg3 u]
    exact hiso (g (g u)) v
  have hzero : g u - g (g u) = 0 := by
    refine hnd.1 _ fun v => ?_
    rw [map_sub, LinearMap.sub_apply, hsa, hshift, sub_self]
  have h1 : g u = g (g u) := sub_eq_zero.1 hzero
  exact (hinj _ _ h1).symm

theorem apply_sub_self_eq {B : BilinForm K V} (hB : B.IsAlt) {g : V →ₗ[K] V}
    (hiso : ∀ x y, B (g x) (g y) = B x y) (hg3 : ∀ x, g (g (g x)) = x) (y : V) :
    B (g (g y - y)) (g y - y) = 3 * B (g y) y := by
  have h1 : B (g (g y)) (g y) = B (g y) y := hiso (g y) y
  have h2 : B (g y) (g y) = 0 := hB.self_eq_zero _
  have h3 : B (g (g y)) y = -B (g y) y := by
    have h := hiso (g (g y)) y
    rw [hg3 y] at h
    rw [← h]
    exact (hB.neg_eq (g y) y).symm
  rw [map_sub g (g y) y]
  simp only [map_sub, LinearMap.sub_apply]
  rw [h1, h2, h3]
  ring

theorem exists_invariant_hyperbolic_pair [Nontrivial V] {B : BilinForm K V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (h3 : (3 : K) ≠ 0) {g : V →ₗ[K] V}
    (hiso : ∀ x y, B (g x) (g y) = B x y) (hg3 : ∀ x, g (g (g x)) = x) :
    ∃ e f : V, B f e = 1 ∧ g e ∈ Submodule.span K {e, f} ∧ g f ∈ Submodule.span K {e, f} := by
  by_cases hid : ∀ y, B (g y) y = 0
  · have hgid := eq_self_of_forall_apply_apply_eq_zero hB hnd hiso hg3 hid
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ : ∃ w, B w e ≠ 0 := by
      by_contra! h
      exact he (hnd.2 e h)
    refine ⟨e, (B w e)⁻¹ • w, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hw]
    · rw [hgid]
      exact Submodule.subset_span (by simp)
    · rw [map_smul, hgid]
      exact Submodule.subset_span (by simp)
  · obtain ⟨y, hy⟩ := not_forall.1 hid
    set e : V := g y - y with he
    have hc : B (g e) e = 3 * B (g y) y := apply_sub_self_eq hB hiso hg3 y
    have hc0 : B (g e) e ≠ 0 := by
      rw [hc]
      exact mul_ne_zero h3 hy
    have hgg : g (g e) = -e - g e := by
      rw [he]
      simp only [map_sub, hg3 y]
      abel
    set c : K := B (g e) e with hcdef
    refine ⟨e, c⁻¹ • g e, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hc0]
    · refine Submodule.mem_span_pair.2 ⟨0, c, ?_⟩
      rw [zero_smul, zero_add, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · refine Submodule.mem_span_pair.2 ⟨-c⁻¹, -1, ?_⟩
      rw [map_smul, hgg]
      simp only [smul_sub, smul_neg, neg_smul, one_smul]
      abel

end Adapted

section Induction

variable {K : Type*} [Field K]

theorem exists_adapted_symplectic_basis (h3 : (3 : K) ≠ 0) :
    ∀ (n : ℕ) (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ (B : BilinForm K V), B.IsAlt → B.Nondegenerate →
      ∀ g : V →ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) → (∀ x, g (g (g x)) = x) →
      ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
        (∀ x y, B (b x) (b y) = Matrix.J (Fin m) K x y) ∧
        ∀ i, ∃ s t u v : K, g (b (Sum.inl i)) = s • b (Sum.inl i) + t • b (Sum.inr i) ∧
          g (b (Sum.inr i)) = u • b (Sum.inl i) + v • b (Sum.inr i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn B hB hnd g hiso hg3
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, Basis.empty V, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  obtain ⟨e, f, hfe, hge, hgf⟩ := exists_invariant_hyperbolic_pair hB hnd h3 hiso hg3
  set Z := B.orthogonal (Submodule.span K {e, f}) with hZ
  have hZn : finrank K Z + 2 = n := hn ▸ hB.finrank_orthogonal_span_pair_add_two hnd hfe
  have hspan : ∀ p ∈ Submodule.span K {e, f}, g p ∈ Submodule.span K {e, f} := by
    intro p hp
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hp
    rw [map_add, map_smul, map_smul]
    exact add_mem (Submodule.smul_mem _ _ hge) (Submodule.smul_mem _ _ hgf)
  have hinv : ∀ z ∈ Z, g z ∈ Z := by
    intro z hz p hp
    have h : B p (g z) = B (g (g p)) z := by
      conv_lhs => rw [← hg3 p]
      exact hiso (g (g p)) z
    show B p (g z) = 0
    rw [h]
    exact hz (g (g p)) (hspan _ (hspan _ hp))
  let gZ : Z →ₗ[K] Z := g.restrict hinv
  obtain ⟨m, c, hc, hcg⟩ := ih (finrank K Z) (by omega) Z rfl (B.restrict Z)
    (fun z => hB.self_eq_zero z) (hB.restrict_nondegenerate_orthogonal_span_pair hfe hnd) gZ
    (fun x y => hiso x y) (fun x => Subtype.ext (hg3 x))
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y := hc
  obtain ⟨b, hb, hbd⟩ := hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hfe c hc'
  refine ⟨m + 1, b, hb, fun i => ?_⟩
  have hbl : ∀ j : Fin m, b (Sum.inl j.succ) = (c (Sum.inl j) : V) := fun j => by
    rw [hbd]; simp
  have hbr : ∀ j : Fin m, b (Sum.inr j.succ) = (c (Sum.inr j) : V) := fun j => by
    rw [hbd]; simp
  have hbl0 : b (Sum.inl 0) = e := by rw [hbd]; simp
  have hbr0 : b (Sum.inr 0) = f := by rw [hbd]; simp
  induction i using Fin.cases with
  | zero =>
    obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 hge
    obtain ⟨u, v, huv⟩ := Submodule.mem_span_pair.1 hgf
    exact ⟨s, t, u, v, by rw [hbl0, hbr0]; exact hst.symm, by rw [hbl0, hbr0]; exact huv.symm⟩
  | succ j =>
    obtain ⟨s, t, u, v, h1, h2⟩ := hcg j
    refine ⟨s, t, u, v, ?_, ?_⟩
    · rw [hbl, hbr]
      exact congrArg Subtype.val h1
    · rw [hbl, hbr]
      exact congrArg Subtype.val h2

end Induction

end Sp6

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
