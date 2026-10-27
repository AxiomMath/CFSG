module

public import TauCeti.GroupTheory.FixedSubgroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

open scoped Pointwise

namespace CFSG.LieType.AlgebraicGroups

variable {G : Type*} [Group G]

theorem exists_fixed_bruhat_factors
    (F : G →* G) (U N : Subgroup G) (V : G → Set G)
    (hU : ∀ u ∈ U, F u ∈ U) (hN : ∀ n ∈ N, F n ∈ N)
    (hV : ∀ n ∈ N, ∀ v ∈ V n, F v ∈ V (F n))
    (hcover : ∀ g : G, ∃ u ∈ U, ∃ n ∈ N, ∃ v ∈ V n, g = u * n * v)
    (hunique : ∀ u ∈ U, ∀ n ∈ N, ∀ v ∈ V n,
      ∀ u' ∈ U, ∀ n' ∈ N, ∀ v' ∈ V n',
      u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v')
    {g : G} (hg : F g = g) :
    ∃ u ∈ U, F u = u ∧ ∃ n ∈ N, F n = n ∧
      ∃ v ∈ V n, F v = v ∧ g = u * n * v := by
  obtain ⟨u, hu, n, hn, v, hv, hmul⟩ := hcover g
  have hprod : F u * F n * F v = u * n * v := by
    rw [← map_mul, ← map_mul, ← hmul, hg]
  obtain ⟨hfu, hfn, hfv⟩ := hunique
    (F u) (hU u hu) (F n) (hN n hn) (F v) (hV n hn v hv)
    u hu n hn v hv hprod
  exact ⟨u, hu, hfu, n, hn, hfn, v, hv, hfv, hmul⟩

theorem fixedSubgroup_le_sup_of_bruhat_coordinates
    (F : G →* G) (U N : Subgroup G) (V : G → Set G)
    (hVU : ∀ n, V n ⊆ U)
    (hU : ∀ u ∈ U, F u ∈ U) (hN : ∀ n ∈ N, F n ∈ N)
    (hV : ∀ n ∈ N, ∀ v ∈ V n, F v ∈ V (F n))
    (hcover : ∀ g : G, ∃ u ∈ U, ∃ n ∈ N, ∃ v ∈ V n, g = u * n * v)
    (hunique : ∀ u ∈ U, ∀ n ∈ N, ∀ v ∈ V n,
      ∀ u' ∈ U, ∀ n' ∈ N, ∀ v' ∈ V n',
      u * n * v = u' * n' * v' → u = u' ∧ n = n' ∧ v = v') :
    TauCeti.fixedSubgroup F ≤
      (U ⊓ TauCeti.fixedSubgroup F) ⊔ (N ⊓ TauCeti.fixedSubgroup F) := by
  intro g hg
  obtain ⟨u, hu, hfu, n, hn, hfn, v, hv, hfv, rfl⟩ :=
    exists_fixed_bruhat_factors F U N V hU hN hV hcover hunique hg
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hu, hfu⟩)
      (Subgroup.mem_sup_right ⟨hn, hfn⟩))
    (Subgroup.mem_sup_left ⟨hVU n hv, hfv⟩)

theorem exists_fixed_factors_of_mem_sup
    (F : G →* G) (T U : Subgroup G)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hdisj : Disjoint T U)
    (hT : ∀ t ∈ T, F t ∈ T) (hU : ∀ u ∈ U, F u ∈ U)
    {g : G} (hg : g ∈ T ⊔ U) (hfg : F g = g) :
    ∃ t ∈ T, F t = t ∧ ∃ u ∈ U, F u = u ∧ g = t * u := by
  have hm : g ∈ (T : Set G) * (U : Set G) := by
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right T U hTU]
  obtain ⟨t, ht, u, hu, hmul⟩ := hm
  change t * u = g at hmul
  have hfactors : (F t)⁻¹ * t = F u * u⁻¹ := by
    apply inv_mul_eq_iff_eq_mul.mpr
    apply (mul_right_cancel (b := u))
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      (show t * u = F t * F u by rw [← map_mul, hmul, hfg])
  have hxT : (F t)⁻¹ * t ∈ T := T.mul_mem (T.inv_mem (hT t ht)) ht
  have hxU : (F t)⁻¹ * t ∈ U := hfactors ▸ U.mul_mem (hU u hu) (U.inv_mem hu)
  have hone := Subgroup.disjoint_def.mp hdisj hxT hxU
  have hft : F t = t := inv_mul_eq_one.mp hone
  have hfu : F u = u := by
    have h : F t * F u = t * u := by rw [← map_mul, hmul, hfg]
    rw [hft] at h
    exact mul_left_cancel h
  exact ⟨t, ht, hft, u, hu, hfu, hmul.symm⟩

theorem sup_inf_fixedSubgroup_eq
    (F : G →* G) (T U : Subgroup G)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hdisj : Disjoint T U)
    (hT : ∀ t ∈ T, F t ∈ T) (hU : ∀ u ∈ U, F u ∈ U) :
    (T ⊔ U) ⊓ TauCeti.fixedSubgroup F =
      (T ⊓ TauCeti.fixedSubgroup F) ⊔ (U ⊓ TauCeti.fixedSubgroup F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t, ht, hft, u, hu, hfu, rfl⟩ :=
      exists_fixed_factors_of_mem_sup F T U hTU hdisj hT hU hg.1 hg.2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ht, hft⟩)
      (Subgroup.mem_sup_right ⟨hu, hfu⟩)
  · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)

end CFSG.LieType.AlgebraicGroups
