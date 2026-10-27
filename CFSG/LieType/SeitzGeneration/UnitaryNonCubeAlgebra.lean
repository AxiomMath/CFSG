module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import CFSG.LieType.SeitzGeneration.UnitaryCubeClasses
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.LieType.SeitzGeneration.NonCube

open Polynomial

variable {K : Type} [Field K]

section Basic

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem minpoly_eq_X_pow_three_sub_C [Nontrivial V] {T : Module.End K V} {α : K}
    (hT : T ^ 3 = algebraMap K (Module.End K V) α) (hc : ¬ ∃ μ : K, μ ^ 3 = α) :
    minpoly K T = X ^ 3 - C α := by
  have hirr := irreducible_X_pow_three_sub_C hc
  symm
  refine minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C _ (by norm_num))
  simp [hT]

theorem eq_zero_of_aeval_eq_zero {T : Module.End K V} {α : K}
    (hT : T ^ 3 = algebraMap K (Module.End K V) α) (hc : ¬ ∃ μ : K, μ ^ 3 = α) {v : V}
    (hv : v ≠ 0) {p : K[X]} (hp : p.degree < 3) (hpv : aeval T p v = 0) : p = 0 := by
  by_contra hp0
  have hirr := irreducible_X_pow_three_sub_C hc
  have hndvd : ¬ (X ^ 3 - C α : K[X]) ∣ p := by
    intro hd
    have h1 := Polynomial.degree_le_of_dvd hd hp0
    rw [degree_X_pow_sub_C (by norm_num)] at h1
    exact absurd hp (not_lt.mpr (by simpa using h1))
  have hcop : IsCoprime (X ^ 3 - C α : K[X]) p := (Irreducible.coprime_iff_not_dvd hirr).2 hndvd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 := congrArg (fun q : K[X] => aeval T q v) hab
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply, map_sub, map_pow, aeval_X, aeval_C] at h1
  rw [hpv, hT] at h1
  simp at h1
  exact hv h1.symm

theorem three_le_finrank_of_stable {T : Module.End K V} {α : K}
    (hT : T ^ 3 = algebraMap K (Module.End K V) α) (hc : ¬ ∃ μ : K, μ ^ 3 = α)
    {S : Submodule K V} (hS : ∀ s ∈ S, T s ∈ S) (hne : S ≠ ⊥) [Module.Finite K S] :
    3 ≤ Module.finrank K S := by
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 : T v ∈ S := hS v hvS
  have h2 : T (T v) ∈ S := hS _ h1
  let b : Fin 3 → S := ![⟨v, hvS⟩, ⟨T v, h1⟩, ⟨T (T v), h2⟩]
  have hind : LinearIndependent K b := by
    apply LinearIndependent.of_comp S.subtype
    rw [Fintype.linearIndependent_iff]
    intro c hc0 i
    have hsum : c 0 • v + c 1 • T v + c 2 • T (T v) = 0 := by
      simpa [Fin.sum_univ_three, b, add_assoc] using hc0
    have hp := eq_zero_of_aeval_eq_zero hT hc hv0 (p := C (c 0) + C (c 1) * X + C (c 2) * X ^ 2)
      (by
        refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (lt_of_le_of_lt (degree_add_le _ _)
          (max_lt ?_ ?_)) ?_)
        · exact lt_of_le_of_lt degree_C_le (by norm_num)
        · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
        · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 2 _) (by norm_num))
      (by simpa [sq, smul_smul, add_assoc, Algebra.smul_def] using hsum)
    fin_cases i
    · simpa using congrArg (fun q : K[X] => q.coeff 0) hp
    · simpa using congrArg (fun q : K[X] => q.coeff 1) hp
    · simpa using congrArg (fun q : K[X] => q.coeff 2) hp
  have := hind.fintype_card_le_finrank
  simpa using this


theorem iSup_eigenspace_eq_top {Y : Module.End K V} {ν ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    (hζ1 : ζ ≠ 1) (hν : ν ≠ 0) (hY : Y ^ 3 = algebraMap K (Module.End K V) (ν ^ 3)) :
    (⨆ j : Fin 3, Module.End.eigenspace Y (ν * ζ ^ (j : ℕ))) = ⊤ := by
  have h3 : (3 : K) ≠ 0 := by
    intro h3
    apply hζ1
    have : (ζ - 1) ^ 2 = 0 := by linear_combination hζ - ζ * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ3
  have hY3 : ∀ v, Y (Y (Y v)) = ν ^ 3 • v := by
    intro v
    have := congrArg (fun T : Module.End K V => T v) hY
    simpa [pow_succ, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one] using this
  rw [eq_top_iff]
  intro v _
  set lam : Fin 3 → K := fun j => ν * ζ ^ (j : ℕ) with hlam
  set θ : Fin 3 → K := fun j => ν⁻¹ * ζ ^ (2 * (j : ℕ)) with hθ
  have hlt : ∀ j, lam j * θ j = 1 := by
    intro j
    simp only [hlam, hθ]
    have h1 : ζ ^ (3 * (j : ℕ)) = 1 := by rw [pow_mul, hζ3, one_pow]
    field_simp
    calc ζ ^ (j : ℕ) * ζ ^ (2 * (j : ℕ)) = ζ ^ (3 * (j : ℕ)) := by rw [← pow_add]; ring_nf
      _ = 1 := h1
  have hl3 : ∀ j, lam j ^ 3 = ν ^ 3 := by
    intro j
    simp only [hlam]
    rw [mul_pow, ← pow_mul, mul_comm (j : ℕ) 3, pow_mul, hζ3, one_pow, mul_one]
  let π : Fin 3 → V := fun j => (3 : K)⁻¹ • (v + θ j • Y v + (θ j) ^ 2 • Y (Y v))
  have hπ : ∀ j, π j ∈ Module.End.eigenspace Y (lam j) := by
    intro j
    rw [Module.End.mem_eigenspace_iff]
    have e1 := hlt j
    have e3 := hl3 j
    simp only [π, map_smul, map_add, hY3]
    match_scalars
    · linear_combination (-(3 : K)⁻¹) * e1
    · linear_combination (-((3 : K)⁻¹ * θ j)) * e1
    · linear_combination (-((3 : K)⁻¹ * θ j ^ 2)) * e3 + ((3 : K)⁻¹ * lam j * (lam j * θ j + 1)) * e1
  have hsum : ∑ j, π j = v := by
    simp only [Fin.sum_univ_three, π, hθ]
    match_scalars
    · have h33 : (3 : K) * 3⁻¹ = 1 := mul_inv_cancel₀ h3
      linear_combination h33
    · simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      linear_combination ((3 : K)⁻¹ * ν⁻¹) * hζ + ((3 : K)⁻¹ * ν⁻¹ * ζ) * hζ3
    · simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      linear_combination ((3 : K)⁻¹ * (ν⁻¹) ^ 2) * hζ + ((3 : K)⁻¹ * (ν⁻¹) ^ 2 * ζ) * hζ3 +
        ((3 : K)⁻¹ * (ν⁻¹) ^ 2 * ζ ^ 2 * (ζ ^ 3 + 1)) * hζ3
  rw [← hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j (hπ j)

end Basic

section Geometry

variable {V : Type*} [AddCommGroup V] [Module K V] {τ : K →+* K}

theorem eigen_orthogonal {B : V →ₛₗ[τ] V →ₗ[K] K} {Y : Module.End K V}
    (hY : ∀ u v, B (Y u) (Y v) = B u v) {l₁ l₂ : K} (hl : τ l₁ * l₂ ≠ 1) {u v : V}
    (hu : Y u = l₁ • u) (hv : Y v = l₂ • v) : B u v = 0 := by
  have h1 := hY u v
  rw [hu, hv] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul] at h1
  have h2 : (τ l₁ * l₂ - 1) * B u v = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hl
  · exact h

theorem separatingLeft_of_orth_iSup {ι : Type*} [Fintype ι] {B : V →ₛₗ[τ] V →ₗ[K] K}
    (hB : B.SeparatingLeft) (W : ι → Submodule K V)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, B u v = 0) (htop : ⨆ i, W i = ⊤) (i : ι) :
    (B.domRestrict₁₂ (W i) (W i)).SeparatingLeft := by
  classical
  intro z hz
  have hz' : ∀ v : V, B (z : V) v = 0 := by
    intro v
    have hv : v ∈ ⨆ j, W j := by rw [htop]; exact Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      by_cases hij : j = i
      · subst hij
        have := hz ⟨x, hx⟩
        rwa [LinearMap.domRestrict₁₂_apply] at this
      · exact horth i j (Ne.symm hij) z z.2 x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  exact Subtype.ext (hB (z : V) hz')

end Geometry


end CFSG.LieType.SeitzGeneration.NonCube
