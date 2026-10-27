module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.F3

open scoped commutatorElement

theorem mem_center_of_commute_map {X H : Type*} [Group X] [Group H] (Θ : X →* H)
    (hker : Θ.ker ≤ Subgroup.center X) (hperf : commutator X = ⊤) {x : X}
    (hx : ∀ y : X, Θ x * Θ y = Θ y * Θ x) : x ∈ Subgroup.center X := by
  have hc : ∀ y : X, ⁅x, y⁆ ∈ Subgroup.center X := by
    intro y
    refine hker ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have h := hx y
    rw [h]
    group
  have hmul : ∀ y y' : X, ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
    intro y y'
    have hb := Subgroup.mem_center_iff.1 (hc y') y
    have hb' : y * ⁅x, y'⁆ * y⁻¹ = ⁅x, y'⁆ := (mul_inv_eq_iff_eq_mul).2 hb
    calc ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = ⁅x, y⁆ * ⁅x, y'⁆ := by rw [hb']
  let f : X →* X := MonoidHom.mk' (fun y => ⁅x, y⁆) hmul
  have hle : commutator X ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have h1 : f g₁ * f g₂ = f g₂ * f g₁ := (Subgroup.mem_center_iff.1 (hc g₁) (f g₂)).symm
    rw [h1]
    group
  rw [hperf] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : f g = 1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g))
  have h2 : ⁅x, g⁆ = 1 := h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm

end CFSG.OddStandard.HigherRank.F3
