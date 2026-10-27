module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilEigen

open Module Polynomial
open scoped Classical

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

@[expose] noncomputable def eigProj (T : Module.End K U) (ξ : K) : Module.End K U :=
  aeval T (Lagrange.basis (nthRootsFinset 5 (1 : K)) id ξ)

theorem eigProj_sum (T : Module.End K U) (ζ : K) (hζ : IsPrimitiveRoot ζ 5) :
    ∑ ξ ∈ nthRootsFinset 5 (1 : K), eigProj T ξ = 1 := by
  unfold eigProj
  rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _), map_one]
  exact ⟨ζ, (mem_nthRootsFinset (by norm_num) 1).mpr hζ.pow_eq_one⟩

theorem eigProj_apply_eigenvector (T : Module.End K U) {ξ ξ' : K}
    (hξ : ξ ∈ nthRootsFinset 5 (1 : K)) {u : U} (hu : T u = ξ • u) :
    eigProj T ξ' u = if ξ' = ξ then u else 0 := by
  unfold eigProj
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hu]
  by_cases h : ξ' = ξ
  · subst h
    have := Lagrange.eval_basis_self (v := id) (s := nthRootsFinset 5 (1 : K)) (i := ξ')
      (Set.injOn_id _) hξ
    simp only [id] at this
    simp [this]
  · have := Lagrange.eval_basis_of_ne (v := id) (s := nthRootsFinset 5 (1 : K)) (i := ξ')
      (j := ξ) h hξ
    simp only [id] at this
    simp [h, this]

theorem eigProj_mem (T : Module.End K U) (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (hT5 : T ^ 5 = 1)
    {ξ : K} (hξ : ξ ∈ nthRootsFinset 5 (1 : K)) (u : U) :
    T (eigProj T ξ u) = ξ • eigProj T ξ u := by
  have h1 : (X - C ξ) * Lagrange.basis (nthRootsFinset 5 (1 : K)) id ξ =
      C (Lagrange.nodalWeight (nthRootsFinset 5 (1 : K)) id ξ) *
        Lagrange.nodal (nthRootsFinset 5 (1 : K)) id := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hξ, ← Lagrange.nodal_erase_eq_nodal_div hξ,
      Lagrange.nodal_eq_mul_nodal_erase hξ]
    simp only [id]
    ring
  have h2 : Lagrange.nodal (nthRootsFinset 5 (1 : K)) id = X ^ 5 - 1 := by
    rw [X_pow_sub_one_eq_prod (by norm_num) hζ, Lagrange.nodal_eq]
    rfl
  have h3 : aeval T ((X - C ξ) * Lagrange.basis (nthRootsFinset 5 (1 : K)) id ξ) = 0 := by
    rw [h1, h2, map_mul, map_sub, map_pow, aeval_X, map_one, hT5, sub_self, mul_zero]
  rw [map_mul, map_sub, aeval_X, aeval_C] at h3
  have h4 := congrArg (fun f => f u) h3
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    LinearMap.zero_apply, sub_eq_zero] at h4
  exact h4

theorem eigProj_comm (T : Module.End K U) (ξ : K) (u : U) :
    eigProj T ξ (T u) = T (eigProj T ξ u) := by
  unfold eigProj
  have h : aeval T (Lagrange.basis (nthRootsFinset 5 (1 : K)) id ξ * X) =
      aeval T (X * Lagrange.basis (nthRootsFinset 5 (1 : K)) id ξ) := by rw [mul_comm]
  simp only [map_mul, aeval_X] at h
  exact congrArg (fun f => f u) h

theorem eigProj_mem_eigenspace (T : Module.End K U) (ζ : K) (hζ : IsPrimitiveRoot ζ 5)
    (hT5 : T ^ 5 = 1) {ξ : K} (hξ : ξ ∈ nthRootsFinset 5 (1 : K)) (u : U) :
    eigProj T ξ u ∈ Module.End.eigenspace T ξ :=
  Module.End.mem_eigenspace_iff.mpr (eigProj_mem T ζ hζ hT5 hξ u)

theorem finrank_le_sum_finrank_eigenspace [FiniteDimensional K U] (T : Module.End K U) (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) (hT5 : T ^ 5 = 1) :
    finrank K U ≤ ∑ ξ ∈ nthRootsFinset 5 (1 : K), finrank K (Module.End.eigenspace T ξ) := by
  set R := nthRootsFinset 5 (1 : K) with hR
  let E : ↥R → Submodule K U := fun ξ => Module.End.eigenspace T ξ
  let Ψ : (∀ ξ : ↥R, ↥(E ξ)) →ₗ[K] U := ∑ ξ : ↥R, (E ξ).subtype.comp (LinearMap.proj ξ)
  have hsurj : Function.Surjective Ψ := by
    intro u
    refine ⟨fun ξ => ⟨eigProj T ξ u, eigProj_mem_eigenspace T ζ hζ hT5 ξ.2 u⟩, ?_⟩
    simp only [Ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply]
    rw [Finset.sum_coe_sort R (fun ξ => eigProj T ξ u)]
    have := congrArg (fun f => f u) (eigProj_sum T ζ hζ)
    simpa [LinearMap.sum_apply] using this
  have h1 := LinearMap.finrank_range_le Ψ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi_fintype] at h1
  rwa [Finset.sum_coe_sort R (fun ξ => finrank K (Module.End.eigenspace T ξ))] at h1

theorem sum_sq_finrank_eigenspace_le [FiniteDimensional K U] (T : Module.End K U) (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) (hT5 : T ^ 5 = 1) (F : Submodule K (Module.End K U))
    (hF : ∀ a : Module.End K U, a ∈ F ↔ T * a = a * T) :
    ∑ ξ ∈ nthRootsFinset 5 (1 : K), (finrank K (Module.End.eigenspace T ξ)) ^ 2 ≤
      finrank K F := by
  set R := nthRootsFinset 5 (1 : K) with hR
  let E : ↥R → Submodule K U := fun ξ => Module.End.eigenspace T ξ
  let P : ∀ ξ : ↥R, U →ₗ[K] ↥(E ξ) := fun ξ =>
    (eigProj T ξ).codRestrict (E ξ) (eigProj_mem_eigenspace T ζ hζ hT5 ξ.2)
  have hP : ∀ (ξ : ↥R) (u : U), ((P ξ u : ↥(E ξ)) : U) = eigProj T ξ u := fun _ _ => rfl
  let Φ : (∀ ξ : ↥R, Module.End K ↥(E ξ)) →ₗ[K] Module.End K U :=
    { toFun := fun b => ∑ ξ : ↥R, (E ξ).subtype ∘ₗ b ξ ∘ₗ P ξ
      map_add' := fun b c => by
        simp only [Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]
      map_smul' := fun r b => by
        simp only [Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum,
          RingHom.id_apply] }
  have hΦ : ∀ (b : ∀ ξ : ↥R, Module.End K ↥(E ξ)) (u : U),
      Φ b u = ∑ ξ : ↥R, ((b ξ (P ξ u) : ↥(E ξ)) : U) := fun b u => by
    simp [Φ, LinearMap.sum_apply]
  have hcomm : ∀ b, T * Φ b = Φ b * T := by
    intro b
    ext u
    simp only [Module.End.mul_apply]
    rw [hΦ, hΦ, map_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have h1 : P ξ (T u) = (ξ : K) • P ξ u := Subtype.ext (by
      rw [hP, Submodule.coe_smul, hP, eigProj_comm, eigProj_mem T ζ hζ hT5 ξ.2])
    rw [h1, map_smul]
    exact (Module.End.mem_eigenspace_iff.mp (b ξ (P ξ u)).2)
  let Φ' : (∀ ξ : ↥R, Module.End K ↥(E ξ)) →ₗ[K] ↥F :=
    Φ.codRestrict F (fun b => (hF _).mpr (hcomm b))
  have hinj : Function.Injective Φ' := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hb0 : Φ b = 0 := congrArg Subtype.val hb
    funext ξ'
    refine LinearMap.ext fun w => ?_
    have h1 := congrArg (fun f => f (w : U)) hb0
    simp only [hΦ, LinearMap.zero_apply] at h1
    rw [Finset.sum_eq_single ξ'] at h1
    · have hw : P ξ' (w : U) = w := Subtype.ext (by
        rw [hP, eigProj_apply_eigenvector T ξ'.2 (Module.End.mem_eigenspace_iff.mp w.2)]
        simp)
      rw [hw] at h1
      exact Subtype.ext h1
    · intro ξ _ hξ
      have hw : P ξ (w : U) = 0 := Subtype.ext (by
        rw [hP, eigProj_apply_eigenvector T ξ'.2 (Module.End.mem_eigenspace_iff.mp w.2)]
        have : (ξ : K) ≠ ξ' := fun h => hξ (Subtype.ext h)
        simp [this])
      rw [hw, map_zero]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at h1
  have h2 : ∀ ξ : ↥R, finrank K (Module.End K ↥(E ξ)) = (finrank K ↥(E ξ)) ^ 2 := fun ξ => by
    rw [sq]
    exact Module.finrank_linearMap K K _ _
  simp only [h2] at h1
  rwa [Finset.sum_coe_sort R (fun ξ => (finrank K (Module.End.eigenspace T ξ)) ^ 2)] at h1

end CFSG.CGT.PushingUpLit.CGT6.WeilEigen
