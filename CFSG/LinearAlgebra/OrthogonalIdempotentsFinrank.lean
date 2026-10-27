module

import TauCeti.LinearAlgebra.Dimension.DirectSum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.LinearAlgebra

theorem sum_finrank_range_le {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] {f : ι → Module.End K V}
    (hf : OrthogonalIdempotents f) :
    (∑ i, Module.finrank K (LinearMap.range (f i))) ≤ Module.finrank K V := by
  have hInd : iSupIndep fun i => LinearMap.range (f i) := by
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨u, rfl⟩ := hv
    have hle : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (f j)) ≤ LinearMap.ker (f i) :=
      iSup₂_le fun j hj => by
        rintro _ ⟨w, rfl⟩
        rw [LinearMap.mem_ker, ← Module.End.mul_apply, hf.ortho (Ne.symm hj),
          LinearMap.zero_apply]
    have h1 := hle hv'
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, (hf.idem i).eq] at h1
    exact h1
  calc
    (∑ i, Module.finrank K (LinearMap.range (f i))) =
        Module.finrank K ↥(⨆ i, LinearMap.range (f i)) :=
      (TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hInd).symm
    _ ≤ Module.finrank K V := Submodule.finrank_le _

theorem finrank_range_conj_of_inv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e e' : V →ₗ[K] V) (he' : e'.comp e = 1)
    (f : Module.End K V) :
    Module.finrank K (LinearMap.range (e * f * e')) =
      Module.finrank K (LinearMap.range f) := by
  have hleft : ∀ x : V, e' (e x) = x := by
    intro x
    have h := congrArg (fun g : V →ₗ[K] V => g x) he'
    simpa [LinearMap.comp_apply] using h
  have hinj : Function.Injective e := by
    intro x y hxy
    have h := congrArg e' hxy
    rwa [hleft x, hleft y] at h
  have hrange : LinearMap.range (e * f * e') = (LinearMap.range f).map e := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      exact ⟨f (e' u), ⟨e' u, rfl⟩, rfl⟩
    · rintro x ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by
        simp only [Module.End.mul_apply]
        rw [hleft u]⟩
  rw [hrange]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e hinj (LinearMap.range f))).symm

end CFSG.LinearAlgebra
