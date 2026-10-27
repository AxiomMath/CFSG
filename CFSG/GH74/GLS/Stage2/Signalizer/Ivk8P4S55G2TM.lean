module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

variable {p : ℕ} {Y : Type} [Group Y]

theorem isPGroup_zpowers_of_orderOf {t : Y} {r : ℕ} (ht : orderOf t = r) :
    IsPGroup r ↥(Subgroup.zpowers t) := by
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (x : Y) ^ r ^ 1 = 1
  rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht,
    pow_orderOf_eq_one, one_zpow]

theorem false_of_torus_moved_pow {α h f : MulAut Y} (hα : α = h * f * h⁻¹) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) {t : Y} (hot : orderOf t = r) {k : ℕ}
    (hft : f t = t ^ k) (hne : f t ≠ t)
    (hHH : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, α x ∈ Q) → ∀ x ∈ Q, α x = x) : False := by
  refine false_of_torus_moved hα hr hr2 hrp (isPGroup_zpowers_of_orderOf hot) ?_
    (Subgroup.mem_zpowers t) hne hHH
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [map_zpow, hft, ← zpow_natCast, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) _

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
