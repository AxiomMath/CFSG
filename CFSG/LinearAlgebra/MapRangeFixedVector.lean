module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice

import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LinearAlgebra

theorem exists_mapRange_fixed_mem_not_mem {σ : Type*} [Finite σ] {k : Type*} [Field k]
    (φ : k →+* k) {W W' : Submodule k (σ →₀ k)}
    (hW : ∀ v ∈ W, Finsupp.mapRange φ φ.map_zero v ∈ W) (hWW' : ¬ W ≤ W') :
    ∃ v ∈ W, v ∉ W' ∧ Finsupp.mapRange φ φ.map_zero v = v := by
  classical
  have : Module.Finite k (σ →₀ k) := Module.Finite.finsupp
  have : Module.Free k W := Module.Free.of_divisionRing k W
  have : Module.Projective k W := Module.Projective.of_free
  let f : σ → Module.Dual k W := fun j => (Finsupp.lapply j).comp W.subtype
  have hfmem : ∀ z : W, z ≠ 0 → ∃ j, f j z ≠ 0 := by
    intro z hz
    by_contra h
    push Not at h
    refine hz (Subtype.ext ?_)
    ext j
    simpa [f] using h j
  have hspan : Submodule.span k (Set.range f) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero (R := k) (M := W) ?_
    intro z hz
    obtain ⟨j, hj⟩ := hfmem z hz
    exact ⟨f j, ⟨j, rfl⟩, hj⟩
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' k f
  have : Finite κ := Finite.of_injective a ha
  let B : Module.Basis κ k (Module.Dual k W) :=
    Module.Basis.mk hli (le_of_eq (hspan'.trans hspan).symm)
  let w : κ → W := fun i => (Module.evalEquiv k W).symm (B.dualBasis i)
  have hwB : ∀ i j, B j (w i) = if j = i then 1 else 0 := by
    intro i j
    rw [Module.apply_evalEquiv_symm_apply]
    exact B.dualBasis_apply_self i j
  let T : κ → W := fun i =>
    ⟨Finsupp.mapRange φ φ.map_zero (w i : σ →₀ k), hW _ (w i).2⟩
  have hBfix : ∀ i j, B j (T i) = B j (w i) := by
    intro i j
    have hcoe : B j = f (a j) := by simp [B]
    have hleft : B j (T i) = φ (B j (w i)) := by
      rw [hcoe]
      show (Finsupp.mapRange φ φ.map_zero (w i : σ →₀ k)) (a j) =
        φ ((w i : σ →₀ k) (a j))
      rw [Finsupp.mapRange_apply]
    rw [hleft, hwB i j]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  have hT : ∀ i, T i = w i := by
    intro i
    apply (Module.evalEquiv k W).injective
    apply B.ext
    intro j
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
    exact hBfix i j
  have hTfix : ∀ i, Finsupp.mapRange φ φ.map_zero (w i : σ →₀ k) = w i := fun i =>
    congrArg Subtype.val (hT i)
  let C : Module.Basis κ k W := B.dualBasis.map (Module.evalEquiv k W).symm
  have hCw : ∀ i, C i = w i := fun i => rfl
  have hspanw : W ≤ Submodule.span k (Set.range fun i => (w i : σ →₀ k)) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : W) ∈ Submodule.span k (Set.range C) := by
      rw [C.span_eq]
      exact Submodule.mem_top
    have himg : (W.subtype : W →ₗ[k] (σ →₀ k)) '' Set.range C =
        Set.range fun i => (w i : σ →₀ k) := by
      rw [← Set.range_comp]
      congr 1
    have hmem : W.subtype (⟨x, hx⟩ : W) ∈
        Submodule.map W.subtype (Submodule.span k (Set.range C)) :=
      Submodule.mem_map_of_mem hx'
    rwa [Submodule.map_span, himg] at hmem
  by_cases h : ∃ i, (w i : σ →₀ k) ∉ W'
  · obtain ⟨i, hi⟩ := h
    exact ⟨w i, (w i).2, hi, hTfix i⟩
  · push Not at h
    exact absurd (fun x hx => Submodule.span_le.mpr (Set.range_subset_iff.mpr h) (hspanw hx)) hWW'

end CFSG.LinearAlgebra
