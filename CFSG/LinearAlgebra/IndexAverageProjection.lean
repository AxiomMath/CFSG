module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap

public section

namespace CFSG.LinearAlgebra.IndexAverage

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

noncomputable def cosetConj (ρ : G →* Module.End K V) (H : Subgroup G) (p : V →ₗ[K] V)
    (c : G ⧸ H) : V →ₗ[K] V :=
  ρ c.out ∘ₗ p ∘ₗ ρ c.out⁻¹

theorem cosetConj_eq (ρ : G →* Module.End K V) (H : Subgroup G) (p : V →ₗ[K] V)
    (hpH : ∀ h ∈ H, ∀ v, p (ρ h v) = ρ h (p v)) (g : G) (v : V) :
    cosetConj ρ H p (g : G ⧸ H) v = ρ g (p (ρ g⁻¹ v)) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  have e : ρ (g * h)⁻¹ v = ρ (h : G)⁻¹ (ρ g⁻¹ v) := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  change ρ (g : G ⧸ H).out (p (ρ (g : G ⧸ H).out⁻¹ v)) = _
  rw [hh, e, hpH _ (H.inv_mem h.2), map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (ρ (h : G)), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem cosetConj_smul (ρ : G →* Module.End K V) (H : Subgroup G) (p : V →ₗ[K] V)
    (hpH : ∀ h ∈ H, ∀ v, p (ρ h v) = ρ h (p v)) (g₀ : G) (c : G ⧸ H) (v : V) :
    cosetConj ρ H p (g₀ • c) (ρ g₀ v) = ρ g₀ (cosetConj ρ H p c v) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetConj_eq ρ H p hpH,
    cosetConj_eq ρ H p hpH]
  have h1 : ρ (g₀ * g)⁻¹ (ρ g₀ v) = ρ g⁻¹ v := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (ρ g₀⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h1, map_mul, Module.End.mul_apply]

theorem exists_equivariant_projection_of_index (ρ : G →* Module.End K V) (H : Subgroup G)
    [H.FiniteIndex] (hn : (H.index : K) ≠ 0) (A : Submodule K V)
    (hA : ∀ g, ∀ a ∈ A, ρ g a ∈ A) (p : V →ₗ[K] V) (hpA : ∀ v, p v ∈ A)
    (hpid : ∀ a ∈ A, p a = a) (hpH : ∀ h ∈ H, ∀ v, p (ρ h v) = ρ h (p v)) :
    ∃ p' : V →ₗ[K] V, (∀ v, p' v ∈ A) ∧ (∀ a ∈ A, p' a = a) ∧
      ∀ g v, p' (ρ g v) = ρ g (p' v) := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let F := cosetConj ρ H p
  refine ⟨(H.index : K)⁻¹ • ∑ c : G ⧸ H, F c, fun v => ?_, fun a ha => ?_, fun g v => ?_⟩
  · have hFv : ∀ c : G ⧸ H, F c v ∈ A := fun c => hA _ _ (hpA _)
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    exact A.smul_mem _ (A.sum_mem fun c _ => hFv c)
  · rw [LinearMap.smul_apply, LinearMap.sum_apply]
    have hF : ∀ c : G ⧸ H, F c a = a := by
      intro c
      change ρ c.out (p (ρ c.out⁻¹ a)) = a
      rw [hpid _ (hA _ a ha), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simp only [hF, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  · rw [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    congr 1
    rw [← Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (G ⧸ H))]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact cosetConj_smul ρ H p hpH g c v

end CFSG.LinearAlgebra.IndexAverage
