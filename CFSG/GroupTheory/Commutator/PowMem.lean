module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem pow_mem_of_commutator_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {a b : H}
    {n : ℕ} (hab : ⁅a, b⁆ ∈ N) (ha : a ^ n ∈ N) (habn : (a * b) ^ n ∈ N) : b ^ n ∈ N := by
  have hcomm : Commute ((QuotientGroup.mk' N) a) ((QuotientGroup.mk' N) b) := by
    show (QuotientGroup.mk' N) a * (QuotientGroup.mk' N) b =
      (QuotientGroup.mk' N) b * (QuotientGroup.mk' N) a
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h3 : a⁻¹ * ⁅a, b⁆⁻¹ * a ∈ N :=
      Subgroup.Normal.conj_mem' inferInstance (⁅a, b⁆⁻¹) (N.inv_mem hab) a
    have h4 : b⁻¹ * (a⁻¹ * ⁅a, b⁆⁻¹ * a) * b ∈ N :=
      Subgroup.Normal.conj_mem' inferInstance (a⁻¹ * ⁅a, b⁆⁻¹ * a) h3 b
    have heq : b⁻¹ * (a⁻¹ * ⁅a, b⁆⁻¹ * a) * b = (a * b)⁻¹ * (b * a) := by
      rw [commutatorElement_def]; group
    rwa [heq] at h4
  have h1 : ((QuotientGroup.mk' N) (a * b)) ^ n = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact habn
  have h2 : ((QuotientGroup.mk' N) a) ^ n = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact ha
  have h3 : ((QuotientGroup.mk' N) (a * b)) ^ n =
      ((QuotientGroup.mk' N) a) ^ n * ((QuotientGroup.mk' N) b) ^ n := by
    rw [map_mul]
    exact hcomm.mul_pow n
  rw [h3, h2, one_mul] at h1
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_pow]
  exact h1

end CFSG.GroupTheory
