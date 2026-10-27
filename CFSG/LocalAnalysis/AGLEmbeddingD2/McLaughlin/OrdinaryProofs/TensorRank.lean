module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Center
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.AGLEmbeddingD2.McLaughlin

open TensorProduct

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

noncomputable def rhoFun (ψ : Module.Dual K V) : V ⊗[K] W →ₗ[K] W :=
  TensorProduct.lift
    (LinearMap.mk₂ K (fun x w => ψ x • w)
      (fun m₁ m₂ n => by
        show ψ (m₁ + m₂) • n = ψ m₁ • n + ψ m₂ • n
        rw [map_add, add_smul])
      (fun c m n => by
        show ψ (c • m) • n = c • (ψ m • n)
        rw [map_smul, smul_eq_mul, mul_smul])
      (fun m n₁ n₂ => by
        show ψ m • (n₁ + n₂) = ψ m • n₁ + ψ m • n₂
        rw [smul_add])
      (fun c m n => by
        show ψ m • (c • n) = c • (ψ m • n)
        rw [smul_comm]))

theorem rhoFun_tmul (ψ : Module.Dual K V) (x : V) (w : W) :
    rhoFun ψ (x ⊗ₜ w) = ψ x • w := by
  simp [rhoFun]

theorem finrank_le_finrank_range_tensor_sub_one
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : V →ₗ[K] V) (B : W →ₗ[K] W) (hA : ∃ v : V, ∀ c : K, A v ≠ c • v) :
    Module.finrank K W ≤
      Module.finrank K
        (LinearMap.range (TensorProduct.map A B - LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W)) := by
  obtain ⟨v, hv⟩ := hA
  have hv0 : v ≠ 0 := by
    intro h
    apply hv 0
    simp [h]
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual K V, χ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff K v).mp h)
  obtain ⟨φ, hφv, hφA⟩ : ∃ φ : Module.Dual K V, φ v = 0 ∧ φ (A v) ≠ 0 := by
    have hnot : (Submodule.Quotient.mk (A v) : V ⧸ Submodule.span K {v}) ≠ 0 := by
      rw [Ne, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
      rintro ⟨c, hc⟩
      exact hv c hc.symm
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K (V ⧸ Submodule.span K {v}),
        ψ (Submodule.Quotient.mk (A v)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hnot ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
    refine ⟨ψ.comp (Submodule.span K {v}).mkQ, ?_, ?_⟩
    · have hmk : (Submodule.Quotient.mk v : V ⧸ Submodule.span K {v}) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_span_singleton_self v
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [hmk, map_zero]
    · simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      exact hψ
  let F : W →ₗ[K] LinearMap.range
      (TensorProduct.map A B - LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W) :=
    LinearMap.codRestrict _
      ((TensorProduct.map A B - LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W).comp
        (TensorProduct.mk K V W v))
      (fun w => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hw' : A v ⊗ₜ[K] B w = v ⊗ₜ[K] w := by
      have h0 := congrArg Subtype.val hw
      simp only [F, LinearMap.codRestrict_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
        LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_zero] at h0
      exact sub_eq_zero.mp h0
    have hBw : B w = 0 := by
      have h1 := congrArg (rhoFun φ) hw'
      simp only [rhoFun_tmul, hφv, zero_smul] at h1
      exact (smul_eq_zero.mp h1).resolve_left hφA
    have h2 := congrArg (rhoFun χ) hw'
    simp only [rhoFun_tmul, hBw, smul_zero] at h2
    exact (smul_eq_zero.mp h2.symm).resolve_left hχ
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem exists_witness_of_not_scalar (A : V →ₗ[K] V) (hA : ∀ a : K, A ≠ a • LinearMap.id) :
    ∃ v : V, ∀ c : K, A v ≠ c • v := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := A) (fun v hli => by
      obtain ⟨c, hc⟩ := h v
      have hdep := (LinearIndependent.pair_iff.mp hli) c (-1)
        (by rw [hc, neg_one_smul, add_neg_cancel])
      exact (neg_ne_zero.mpr one_ne_zero) hdep.2)
  exact hA a (by rw [ha]; rfl)

theorem finrank_le_finrank_range_tensor_sub_one_of_not_scalar
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : V →ₗ[K] V) (B : W →ₗ[K] W) (hA : ∀ a : K, A ≠ a • LinearMap.id) :
    Module.finrank K W ≤
      Module.finrank K
        (LinearMap.range (TensorProduct.map A B - LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W)) :=
  finrank_le_finrank_range_tensor_sub_one A B (exists_witness_of_not_scalar A hA)

end CFSG.AGLEmbeddingD2.McLaughlin

end
