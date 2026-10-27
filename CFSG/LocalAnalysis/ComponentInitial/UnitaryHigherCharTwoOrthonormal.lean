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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open LinearMap (BilinForm)
open Module

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

theorem exists_norm_one_of_charTwo (hsq : ∀ a : K, IsSquare a) {B : BilinForm K V}
    (hB : B.IsSymm) (hnd : B.Nondegenerate) {x : V} (hx : B x x ≠ 0) :
    ∃ e : V, B e e = 1 ∧
      (B.orthogonal (K ∙ e) = ⊥ ∨ ∃ y ∈ B.orthogonal (K ∙ e), B y y ≠ 0) := by
  obtain ⟨s, hs⟩ := hsq (B x x)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact hx hs
  set e₀ := s⁻¹ • x with he₀def
  have he₀ : B e₀ e₀ = 1 := by
    simp only [he₀def, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hs]
    field_simp
  by_cases hW : B.orthogonal (K ∙ e₀) = ⊥ ∨ ∃ y ∈ B.orthogonal (K ∙ e₀), B y y ≠ 0
  · exact ⟨e₀, he₀, hW⟩
  push Not at hW
  obtain ⟨hW0, hWalt⟩ := hW
  have he₀0 : B e₀ e₀ ≠ 0 := by
    rw [he₀]
    exact one_ne_zero
  have hortho : ∀ z ∈ B.orthogonal (K ∙ e₀), B e₀ z = 0 := fun z hz =>
    BilinForm.mem_orthogonal_iff.mp hz e₀ (Submodule.mem_span_singleton_self e₀)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨w, hw, huw⟩ : ∃ w ∈ B.orthogonal (K ∙ e₀), B u w ≠ 0 := by
    have hnd' := B.restrict_nondegenerate_orthogonal_spanSingleton hnd hB.isRefl he₀0
    by_contra hall
    push Not at hall
    have h0 := hnd'.1 ⟨u, hu⟩ fun z => by
      rw [BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      exact hall z z.2
    exact hu0 (congrArg Subtype.val h0)
  set v := (B u w)⁻¹ • w with hvdef
  have hv : v ∈ B.orthogonal (K ∙ e₀) := Submodule.smul_mem _ _ hw
  have huv : B u v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ huw]
  have huu := hWalt u hu
  have hvv := hWalt v hv
  have he₀u := hortho u hu
  have he₀v := hortho v hv
  have hue₀ : B u e₀ = 0 := by rw [hB.eq, he₀u]
  have hve₀ : B v e₀ = 0 := by rw [hB.eq, he₀v]
  refine ⟨e₀ + u, ?_, Or.inr ⟨e₀ + v, ?_, ?_⟩⟩
  · simp only [map_add, LinearMap.add_apply, he₀, he₀u, hue₀, huu, add_zero]
  · rw [BilinForm.mem_orthogonal_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply, he₀, he₀v, hue₀,
      huv, add_zero, zero_add, CharTwo.add_self_eq_zero]
  · simp only [map_add, LinearMap.add_apply, he₀, he₀v, hve₀, hvv, add_zero]
    exact one_ne_zero

theorem exists_orthonormal_basis_of_charTwo (hsq : ∀ a : K, IsSquare a) [FiniteDimensional K V]
    {B : BilinForm K V} (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (halt : finrank K V = 0 ∨ ∃ x, B x x ≠ 0) :
    ∃ b : Basis (Fin (finrank K V)) K V, ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  induction hd : finrank K V generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i => i.elim0⟩
  | succ d ih =>
    obtain ⟨x, hx⟩ := halt.resolve_left (by omega)
    obtain ⟨e, he, hcompl⟩ := exists_norm_one_of_charTwo hsq hB hnd hx
    have he0 : B e e ≠ 0 := by
      rw [he]
      exact one_ne_zero
    have hene : e ≠ 0 := fun h0 => he0 (by rw [h0, map_zero])
    have hIC := BilinForm.isCompl_span_singleton_orthogonal he0
    have hdW : finrank K (B.orthogonal (K ∙ e)) = d := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hIC
      rw [finrank_span_singleton hene, hd] at h1
      omega
    have hsymm' : (B.restrict (B.orthogonal (K ∙ e))).IsSymm := ⟨fun y z => hB.eq y z⟩
    have hnd' := B.restrict_nondegenerate_orthogonal_spanSingleton hnd hB.isRefl he0
    have halt' : finrank K (B.orthogonal (K ∙ e)) = 0 ∨
        ∃ y, B.restrict (B.orthogonal (K ∙ e)) y y ≠ 0 := by
      rcases hcompl with h0 | ⟨y, hy, hyy⟩
      · left
        rw [h0]
        exact finrank_bot K V
      · exact Or.inr ⟨⟨y, hy⟩, hyy⟩
    obtain ⟨b', hb'⟩ := ih hsymm' hnd' halt' hdW
    have hortho : ∀ z ∈ B.orthogonal (K ∙ e), B e z = 0 := fun z hz =>
      BilinForm.mem_orthogonal_iff.mp hz e (Submodule.mem_span_singleton_self e)
    refine ⟨Basis.mkFinCons e b' (fun c y hy hc => ?_) (fun z => ⟨-B e z, ?_⟩), ?_⟩
    · have hce : c • e ∈ B.orthogonal (K ∙ e) := by
        rw [eq_neg_of_add_eq_zero_left hc]
        exact Submodule.neg_mem _ hy
      have h0 := Submodule.disjoint_def.mp hIC.disjoint (c • e)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)) hce
      exact (smul_eq_zero.mp h0).resolve_right hene
    · rw [BilinForm.mem_orthogonal_iff]
      intro y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp only [map_smul, LinearMap.smul_apply, map_add, he, smul_eq_mul, mul_one]
      ring
    · rw [Basis.coe_mkFinCons]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [he]
      · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
        simp [hortho _ (b' j).2, (Fin.succ_ne_zero j).symm]
      · simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
        rw [hB.eq, hortho _ (b' i).2]
        simp [Fin.succ_ne_zero i]
      · simp only [Fin.cons_succ, Function.comp_apply, Fin.succ_inj]
        exact hb' i j

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
