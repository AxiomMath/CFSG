module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

theorem exists_sylow_forall_smul_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] (e : X ≃* Y) (A : Subgroup (MulAut X)) (ω' : Sylow p Y)
    (hω' : ∀ a ∈ A, MulAut.congr e a • ω' = ω') :
    ∃ ω : Sylow p X, ∀ a ∈ A, a • ω = ω := by
  have hf : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  let ω : Sylow p X := ω'.mapSurjective hf
  have hωcoe : (ω : Subgroup X) = (ω' : Subgroup Y).map e.symm.toMonoidHom := by
    simp [ω]
  have hmem : ∀ y : X, y ∈ (ω : Subgroup X) ↔ e y ∈ (ω' : Subgroup Y) := by
    intro y
    rw [hωcoe, Subgroup.mem_map_equiv]
    simp
  refine ⟨ω, ?_⟩
  intro a ha
  have hcoe : (MulAut.congr e a) • (ω' : Subgroup Y) = (ω' : Subgroup Y) := by
    simpa [Sylow.pointwise_smul_def] using
      congrArg (fun S : Sylow p Y => (S : Subgroup Y)) (hω' a ha)
  apply Sylow.ext
  ext x
  rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem]
  have hx : e (a⁻¹ • x) = (MulAut.congr e a)⁻¹ • e x := by
    simp [MulAut.congr_apply, MulAut.smul_def]
  rw [hx]
  constructor
  · intro h
    have h1 : e x ∈ (MulAut.congr e a) • (ω' : Subgroup Y) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      exact h
    rwa [hcoe] at h1
  · intro h
    have h1 : e x ∈ (MulAut.congr e a) • (ω' : Subgroup Y) := by rwa [hcoe]
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1

theorem mem_normalizer_smul_sylow_of_apply_eq {X : Type*} [Group X] {p : ℕ} (a : MulAut X)
    {y : X} (ha : a y = y) {P : Sylow p X}
    (hP : y ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)) :
    y ∈ Subgroup.normalizer (((a • P : Sylow p X) : Subgroup X) : Set X) := by
  have hcoe : ((a • P : Sylow p X) : Subgroup X) = (P : Subgroup X).map a.toMonoidHom := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hmem : a y ∈ (Subgroup.normalizer ((P : Subgroup X) : Set X)).map a.toMonoidHom :=
    ⟨y, hP, rfl⟩
  rw [Subgroup.map_equiv_normalizer_eq] at hmem
  rw [hcoe]
  simpa [ha] using hmem

end CFSG.GroupTheory
