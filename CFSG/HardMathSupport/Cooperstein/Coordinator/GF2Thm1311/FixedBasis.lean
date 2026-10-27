module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_fixedBasis [CharP K 2] {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) {x₀ : K}
    (hx₀ : σ x₀ ≠ x₀) (T : V →ₛₗ[(σ : K →+* K)] V) (hTT : ∀ v, T (T v) = v) :
    ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, T (b i) = b i := by
  classical
  have hden : x₀ + σ x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [eq_neg_of_add_eq_zero_right h, CharTwo.neg_eq]
  set e := x₀ / (x₀ + σ x₀) with he
  have hee : e + σ e = 1 := by
    rw [he, map_div₀, map_add, hσσ, add_comm (σ x₀) x₀, ← add_div, div_self hden]
  set Fix : Set V := {v | T v = v} with hFix
  have hspan : Submodule.span K Fix = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hw₁ : v + T v ∈ Fix := by
      change T (v + T v) = v + T v
      rw [map_add, hTT, add_comm]
    have hw₂ : σ e • v + e • T v ∈ Fix := by
      change T (σ e • v + e • T v) = σ e • v + e • T v
      rw [map_add, map_smulₛₗ, map_smulₛₗ, RingHom.coe_coe, hσσ, hTT, add_comm]
    have h2 : e • T v + e • T v = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hv : v = e • (v + T v) + (σ e • v + e • T v) := by
      calc v = (e + σ e) • v + (e • T v + e • T v) := by rw [hee, one_smul, h2, add_zero]
        _ = _ := by
          rw [smul_add, add_smul]
          abel
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hw₁))
      (Submodule.subset_span hw₂)
  obtain ⟨b, hbFix, hbspan, hbli⟩ := exists_linearIndependent K Fix
  rw [hspan] at hbspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hbspan]
  let bas₀ := Basis.mk hbli hsp
  let _ := FiniteDimensional.fintypeBasisIndex bas₀
  have hcard : Fintype.card b = finrank K V := (Module.finrank_eq_card_basis bas₀).symm
  refine ⟨bas₀.reindex (Fintype.equivFinOfCardEq hcard), fun c => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hbFix (Subtype.mem _)

omit [FiniteDimensional K V] in
theorem repr_semilinear {ι : Type*} [Fintype ι] {σ : K ≃+* K} (b : Basis ι K V)
    (T : V →ₛₗ[(σ : K →+* K)] V) (hb : ∀ i, T (b i) = b i) (v : V) (i : ι) :
    b.repr (T v) i = σ (b.repr v i) := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp only [map_smulₛₗ, RingHom.coe_coe, hb, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  simp [Basis.repr_self, Finsupp.single_apply]

theorem exists_basis_map_toMatrix [CharP K 2] {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) {x₀ : K}
    (hx₀ : σ x₀ ≠ x₀) (T : V →ₛₗ[(σ : K →+* K)] V) (hTT : ∀ v, T (T v) = v) {n : ℕ}
    (hn : finrank K V = n) :
    ∃ b : Basis (Fin n) K V, ∀ f f' : V →ₗ[K] V, (∀ v, T (f v) = f' (T v)) →
      (LinearMap.toMatrix b b f).map σ = LinearMap.toMatrix b b f' := by
  obtain ⟨b, hb⟩ := exists_fixedBasis hσσ hx₀ T hTT
  refine ⟨b.reindex (finCongr hn), fun f f' hf => ?_⟩
  have hb' : ∀ i, T (b.reindex (finCongr hn) i) = b.reindex (finCongr hn) i := fun i => by
    simp [hb]
  ext i j
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
  have h1 := hf ((b.reindex (finCongr hn)) j)
  rw [hb'] at h1
  rw [← repr_semilinear _ T hb', h1]

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
