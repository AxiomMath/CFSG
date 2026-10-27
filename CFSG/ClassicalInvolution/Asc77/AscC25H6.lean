module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
import Mathlib.Tactic.Group

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

section Main

variable {G : Type*} [Group G]

theorem swap_m_facts {a n n' z t' : G} (ht2 : t' * t' = 1) (hti : t'⁻¹ = t') (haz : a * z = z * a)
    (ha2 : a * a = 1) (hsq : z * z = 1) (hat : a * t' = t' * a) (htz : t' * z = z * t')
    (hn' : n' = t' * n * t') :
    t' * (n' * (a * z) * n⁻¹) * t' = (n' * (a * z) * n⁻¹)⁻¹ ∧
      t' * (n' * (a * z) * n⁻¹) = n * (a * z * t') * n⁻¹ := by
  have haz2 : (a * z) * (a * z) = 1 := by
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [← haz]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hsq, mul_one]
  have hazi : (a * z)⁻¹ = a * z := inv_eq_of_mul_eq_one_right haz2
  have hcom : t' * (a * z) = (a * z) * t' := by
    calc t' * (a * z) = (t' * a) * z := by rw [mul_assoc]
      _ = (a * t') * z := by rw [hat]
      _ = a * (t' * z) := by rw [mul_assoc]
      _ = a * (z * t') := by rw [htz]
      _ = (a * z) * t' := by rw [mul_assoc]
  have ht'az : t' * (a * z) * t' = a * z := by rw [hcom, mul_assoc, ht2, mul_one]
  have htn' : t' * n' = n * t' := by
    rw [hn']
    calc t' * (t' * n * t') = (t' * t') * n * t' := by group
      _ = n * t' := by rw [ht2, one_mul]
  have hn'' : t' * n' * t' = n := by rw [htn', mul_assoc, ht2, mul_one]
  have hn'inv : t' * n⁻¹ * t' = n'⁻¹ := by
    rw [hn', mul_inv_rev, mul_inv_rev, hti]
    group
  refine ⟨?_, ?_⟩
  · calc t' * (n' * (a * z) * n⁻¹) * t' =
          (t' * n' * t') * (t' * (a * z) * t') * (t' * n⁻¹ * t') := by
          calc t' * (n' * (a * z) * n⁻¹) * t' =
              t' * n' * (t' * t') * (a * z) * (t' * t') * n⁻¹ * t' := by rw [ht2]; group
            _ = _ := by group
      _ = n * (a * z) * n'⁻¹ := by rw [hn'', ht'az, hn'inv]
      _ = (n' * (a * z) * n⁻¹)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hazi, inv_inv]
          group
  · calc t' * (n' * (a * z) * n⁻¹) = (t' * n') * (a * z) * n⁻¹ := by group
      _ = (n * t') * (a * z) * n⁻¹ := by rw [htn']
      _ = n * (t' * (a * z)) * n⁻¹ := by group
      _ = n * (a * z * t') * n⁻¹ := by rw [hcom]

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
