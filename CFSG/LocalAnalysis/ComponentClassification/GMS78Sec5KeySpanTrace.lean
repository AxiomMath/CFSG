module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

theorem trace_pow_two_pow [CharP K 2] (x : K) (m : ℕ) :
    Algebra.trace (ZMod 2) K (x ^ 2 ^ m) = Algebra.trace (ZMod 2) K x := by
  let f : K ≃+* K := iterateFrobeniusEquiv K 2 m
  let fA : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := f) (fun y => by
    have hcomp : f.toRingHom.comp (algebraMap (ZMod 2) K) = algebraMap (ZMod 2) K :=
      Subsingleton.elim _ _
    exact DFunLike.congr_fun hcomp y)
  have h := Algebra.trace_eq_of_algEquiv fA x
  have hx : fA x = x ^ 2 ^ m := iterateFrobeniusEquiv_def K 2 m x
  rwa [hx] at h

theorem exists_trace_mul_ne_zero {γ : K} (hγ : γ ≠ 0) :
    ∃ y, Algebra.trace (ZMod 2) K (γ * y) ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := Algebra.trace_surjective (ZMod 2) K 1
  exact ⟨y₀ / γ, by rw [mul_div_cancel₀ _ hγ, hy₀]; exact one_ne_zero⟩

theorem eq_zero_of_forall_trace_mul_eq_zero {γ : K}
    (h : ∀ y, Algebra.trace (ZMod 2) K (γ * y) = 0) : γ = 0 := by
  by_contra hγ
  obtain ⟨y, hy⟩ := exists_trace_mul_ne_zero hγ
  exact hy (h y)

theorem exists_eq_trace_mul (f : K →ₗ[ZMod 2] ZMod 2) :
    ∃ δ : K, ∀ y, f y = Algebra.trace (ZMod 2) K (δ * y) := by
  obtain ⟨δ, hδ⟩ :=
    ((Algebra.traceForm (ZMod 2) K).toDual (traceForm_nondegenerate (ZMod 2) K)).surjective f
  refine ⟨δ, fun y => ?_⟩
  have := LinearMap.congr_fun hδ y
  simpa [LinearMap.BilinForm.toDual_def] using this.symm

theorem exists_ne_zero_trace_mul_eq_zero_of_ne_top {H : AddSubgroup K} (hH : H ≠ ⊤) :
    ∃ β : K, β ≠ 0 ∧ ∀ y ∈ H, Algebra.trace (ZMod 2) K (β * y) = 0 := by
  let p : Submodule (ZMod 2) K := AddSubgroup.toZModSubmodule 2 H
  have hp : p < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hH (eq_top_iff.mpr fun y _ => ?_)
    have hy : y ∈ p := h ▸ Submodule.mem_top
    exact hy
  obtain ⟨f, hf0, hpf⟩ := Submodule.exists_le_ker_of_lt_top p hp
  obtain ⟨β, hβ⟩ := exists_eq_trace_mul f
  refine ⟨β, fun h0 => hf0 (LinearMap.ext fun y => ?_), fun y hy => ?_⟩
  · rw [hβ, h0, zero_mul, map_zero, LinearMap.zero_apply]
  · rw [← hβ]
    exact hpf (show y ∈ p from hy)

theorem exists_trace_mul_eq_of_ker_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (M : V →ₗ[ZMod 2] K) (g : V →ₗ[ZMod 2] ZMod 2) (hg : ∀ v, M v = 0 → g v = 0) :
    ∃ δ : K, ∀ v, g v = Algebra.trace (ZMod 2) K (δ * M v) := by
  have hmem : g ∈ (LinearMap.ker M).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator g).mpr fun v hv => hg v hv
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨h, rfl⟩ := hmem
  obtain ⟨δ, hδ⟩ := exists_eq_trace_mul h
  exact ⟨δ, fun v => by rw [LinearMap.dualMap_apply, hδ]⟩

end CFSG.ComponentClassification.GMS78.VLike
