module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sub_one_mapsTo_orthogonal (B : LinearMap.BilinForm K V) {g : V ≃ₗ[K] V}
    (hg : ∀ x y, B (g x) (g y) = B x y) {F F' : Submodule K V}
    (hstep : ∀ y ∈ F', g y - y ∈ F) (hinv : ∀ y ∈ F, g.symm y ∈ F) :
    ∀ x ∈ B.orthogonal F, g x - x ∈ B.orthogonal F' := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  intro y hy
  have hyx : B y (g x) = B (g.symm y) x := by
    rw [← hg (g.symm y) x, LinearEquiv.apply_symm_apply]
  have hmem : g.symm y - y ∈ F := by
    have h := hinv _ (hstep y hy)
    rw [map_sub, LinearEquiv.symm_apply_apply] at h
    have h' := F.neg_mem h
    rwa [neg_sub] at h'
  have h0 : B (g.symm y - y) x = 0 := hx _ hmem
  change B y (g x - x) = 0
  rw [map_sub, hyx]
  rw [map_sub, LinearMap.sub_apply] at h0
  exact h0

theorem sub_one_pow_apply_eq_zero_of_chain {g : V ≃ₗ[K] V} (F : ℕ → Submodule K V)
    (hF0 : F 0 = ⊥) (k : ℕ) (hstep : ∀ i < k, ∀ x ∈ F (i + 1), g x - x ∈ F i) :
    ∀ i ≤ k, ∀ x ∈ F i, (((g : V →ₗ[K] V) - 1) ^ i) x = 0 := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    rw [hF0, Submodule.mem_bot] at hx
    rw [hx, map_zero]
  | succ i ih =>
    intro hi x hx
    rw [pow_succ, Module.End.mul_apply]
    exact ih (by omega) _ (by simpa using hstep i (by omega) x hx)

theorem symm_mem_of_mapsTo [FiniteDimensional K V] {g : V ≃ₗ[K] V} {F : Submodule K V}
    (h : ∀ x ∈ F, g x ∈ F) : ∀ x ∈ F, g.symm x ∈ F := by
  have hle : F.map (g : V →ₗ[K] V) ≤ F := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : F.map (g : V →ₗ[K] V) = F :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g F)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact hy

theorem sub_one_pow_eq_zero_of_isotropic_flag [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) {g : V ≃ₗ[K] V} (hg : ∀ x y, B (g x) (g y) = B x y)
    (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (k : ℕ) (hmono : ∀ i < k, F i ≤ F (i + 1))
    (hstep : ∀ i < k, ∀ x ∈ F (i + 1), g x - x ∈ F i)
    (htop : ∀ x ∈ B.orthogonal (F k), g x - x ∈ F k) :
    ((g : V →ₗ[K] V) - 1) ^ (2 * k + 1) = 0 := by
  set u : V →ₗ[K] V := (g : V →ₗ[K] V) - 1 with hu
  have hux : ∀ x, u x = g x - x := fun x => rfl
  have hA := sub_one_pow_apply_eq_zero_of_chain F hF0 k hstep
  have hgF : ∀ i ≤ k, ∀ x ∈ F i, g x ∈ F i := by
    intro i hi x hx
    rcases i with _ | i
    · rw [hF0, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact zero_mem _
    · have h1 := hmono i (by omega) (hstep i (by omega) x hx)
      have h2 := add_mem h1 hx
      rwa [sub_add_cancel] at h2
  have hinv : ∀ i ≤ k, ∀ x ∈ F i, g.symm x ∈ F i := fun i hi =>
    symm_mem_of_mapsTo (hgF i hi)
  have hC : ∀ j ≤ k, ∀ x ∈ B.orthogonal (F (k - j)), (u ^ (k + 1 + j)) x = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ x hx
      rw [Nat.sub_zero] at hx
      rw [Nat.add_zero, pow_succ, Module.End.mul_apply, hux]
      exact hA k le_rfl _ (htop x hx)
    | succ j ih =>
      intro hj x hx
      have hi : k - j = k - (j + 1) + 1 := by omega
      have hdual := sub_one_mapsTo_orthogonal B hg (F := F (k - (j + 1)))
        (F' := F (k - j)) (by rw [hi]; exact hstep _ (by omega)) (hinv _ (by omega)) x hx
      rw [show k + 1 + (j + 1) = k + 1 + j + 1 by ring, pow_succ, Module.End.mul_apply, hux]
      exact ih (by omega) _ hdual
  ext x
  have h := hC k le_rfl x (by
    rw [Nat.sub_self, hF0, LinearMap.BilinForm.orthogonal_bot]
    exact Submodule.mem_top)
  rw [show 2 * k + 1 = k + 1 + k by ring, h]
  rfl

theorem one_add_pow_two_pow_of_two_eq_zero {R : Type*} [Ring R] (h2 : (2 : R) = 0) (a : R)
    (j : ℕ) : (1 + a) ^ (2 ^ j) = 1 + a ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, (Commute.one_left (a ^ 2 ^ j)).add_sq, one_pow, mul_one, h2,
      zero_mul, add_zero, ← pow_mul]

theorem pow_two_pow_eq_one_of_sub_one_pow_eq_zero [CharP K 2] {g : V ≃ₗ[K] V} {m : ℕ}
    (h : ((g : V →ₗ[K] V) - 1) ^ m = 0) : g ^ (2 ^ m) = 1 := by
  have h2 : (2 : Module.End K V) = 0 := by
    rw [← one_add_one_eq_two, ← two_smul K (1 : Module.End K V), CharTwo.two_eq_zero, zero_smul]
  have hm : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
  have hpow : ((g : V →ₗ[K] V)) ^ (2 ^ m) = 1 := by
    have e : (g : V →ₗ[K] V) = 1 + ((g : V →ₗ[K] V) - 1) := by abel
    rw [e, one_add_pow_two_pow_of_two_eq_zero h2, ← Nat.sub_add_cancel hm, pow_add, h, mul_zero,
      add_zero]
  ext x
  have hx := congrArg (fun f : Module.End K V => f x) hpow
  simp only [Module.End.one_apply] at hx
  rw [LinearEquiv.coe_pow]
  change (⇑g)^[2 ^ m] x = x
  calc (⇑g)^[2 ^ m] x = (((g : V →ₗ[K] V)) ^ (2 ^ m)) x := by
        rw [Module.End.coe_pow]; rfl
    _ = x := hx

theorem isPGroup_two_of_forall_sub_one_pow_eq_zero [CharP K 2] (H : Subgroup (V ≃ₗ[K] V))
    {m : ℕ} (h : ∀ g ∈ H, ((g : V →ₗ[K] V) - 1) ^ m = 0) : IsPGroup 2 H := by
  intro g
  refine ⟨m, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_two_pow_eq_one_of_sub_one_pow_eq_zero (h g g.2)

theorem isPGroup_two_of_flag [CharP K 2] [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (H : Subgroup (V ≃ₗ[K] V)) (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (k : ℕ)
    (hmono : ∀ i < k, F i ≤ F (i + 1))
    (hH : ∀ g ∈ H, (∀ x y, B (g x) (g y) = B x y) ∧
      (∀ i < k, ∀ x ∈ F (i + 1), g x - x ∈ F i) ∧ ∀ x ∈ B.orthogonal (F k), g x - x ∈ F k) :
    IsPGroup 2 H :=
  isPGroup_two_of_forall_sub_one_pow_eq_zero H fun g hg =>
    sub_one_pow_eq_zero_of_isotropic_flag B (hH g hg).1 F hF0 k hmono (hH g hg).2.1 (hH g hg).2.2

end CFSG.SeitzReduction.OmegaPilot
