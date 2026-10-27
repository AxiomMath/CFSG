module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem conj_zpow_neg_reorder {G : Type*} [Group G] {Q : Subgroup G} [IsMulCommutative Q]
    {s y t : G} (hs : s ∈ Subgroup.normalizer Q) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y) (i j : ℤ) :
    (t ^ i)⁻¹ * s ^ (-j) * t ^ i
      = ((t ^ j)⁻¹ * s ^ (-i) * t ^ j) * s ^ (-(j - i)) := by
  have hA : ∀ k : ℤ, s ^ (-k) * y * s ^ k ∈ Q := fun k => by
    simpa [zpow_neg] using (Subgroup.mem_normalizer_iff''.mp (zpow_mem hs k) y).mp hy
  set a : G := s ^ (-i) * y * s ^ i with ha
  set c : G := s ^ (-(i - j)) * y * s ^ (i - j) with hc
  have haQ : a ∈ Q := hA i
  have hcQ : c ∈ Q := hA (i - j)
  have hac : a⁻¹ * c = c * a⁻¹ := setLike_mul_comm (inv_mem haQ) hcQ
  have hyc : y * (a⁻¹ * c) = (a⁻¹ * c) * y :=
    setLike_mul_comm hy (mul_mem (inv_mem haQ) hcQ)
  have htk : ∀ k : ℤ, t ^ k = y⁻¹ * s ^ k * y := fun k => by
    rw [ht, show y⁻¹ * s * y = y⁻¹ * s * y⁻¹⁻¹ by group, conj_zpow]
    group
  calc (t ^ i)⁻¹ * s ^ (-j) * t ^ i
      = y⁻¹ * s ^ (-j) * (c * a⁻¹) * y := by rw [htk i, ha, hc]; group
    _ = y⁻¹ * s ^ (-j) * ((a⁻¹ * c) * y) := by rw [← hac]; group
    _ = y⁻¹ * s ^ (-j) * (y * (a⁻¹ * c)) := by rw [hyc]
    _ = ((t ^ j)⁻¹ * s ^ (-i) * t ^ j) * s ^ (-(j - i)) := by rw [htk j, ha, hc]; group

theorem conj_inv_pow_reorder {G : Type*} [Group G] {Q : Subgroup G} [IsMulCommutative Q]
    {s y t : G} (hs : s ∈ Subgroup.normalizer Q) (hy : y ∈ Q) (ht : t = y⁻¹ * s * y)
    {i j : ℕ} (hij : i ≤ j) :
    (t ^ i)⁻¹ * (s ^ j)⁻¹ * t ^ i
      = ((t ^ j)⁻¹ * (s ^ i)⁻¹ * t ^ j) * (s ^ (j - i))⁻¹ := by
  simpa [zpow_neg, ← Nat.cast_sub hij] using
    conj_zpow_neg_reorder hs hy ht (i : ℤ) (j : ℤ)

end CFSG.FeitThompson
