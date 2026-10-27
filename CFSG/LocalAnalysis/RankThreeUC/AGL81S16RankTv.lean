module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_tv_of_fix_perp (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {g : SUid σ 4}
    (hg2 : g * g = 1) {w₀ : Fin 4 → F} (hw₀ : w₀ ≠ 0)
    (hfix : ∀ x, herm σ w₀ x = 0 → g • x = x) :
    ∃ c : F, c + σ c = 0 ∧ ∀ x, g • x = x + (c * herm σ w₀ x) • w₀ := by
  have hadj : ∀ x y : Fin 4 → F, herm σ (g • x) y = herm σ x (g • y) := by
    intro x y
    have h := herm_smul_smul σ g x (g • y)
    rw [← mul_smul, hg2, one_smul] at h
    exact h
  have hN : ∀ x y : Fin 4 → F, herm σ (g • x - x) y = herm σ x (g • y - y) := by
    intro x y
    rw [herm_sub_left, herm_sub_right, hadj]
  obtain ⟨x₀, hx₀⟩ := exists_herm_eq_one σ hw₀
  have hstep2 : ∀ x : Fin 4 → F, g • x - x = herm σ w₀ x • (g • x₀ - x₀) := by
    intro x
    have hx' : herm σ w₀ (x - herm σ w₀ x • x₀) = 0 := by
      rw [herm_sub_right, herm_smul_right, hx₀, mul_one, sub_self]
    have hfx := hfix _ hx'
    rw [smul_sub, smul_comm g (herm σ w₀ x) x₀] at hfx
    rw [smul_sub]
    have key : g • x - x = (g • x - herm σ w₀ x • g • x₀) - (x - herm σ w₀ x • x₀)
        + (herm σ w₀ x • g • x₀ - herm σ w₀ x • x₀) := by abel
    rw [hfx, sub_self, zero_add] at key
    exact key
  have hperp : ∀ y : Fin 4 → F, herm σ w₀ y = 0 → herm σ (g • x₀ - x₀) y = 0 := by
    intro y hy
    rw [hN x₀ y, hstep2 y, hy, zero_smul, herm_zero_right]
  have hm_lin : ∀ y : Fin 4 → F,
      herm σ (g • x₀ - x₀) y = herm σ (g • x₀ - x₀) x₀ * herm σ w₀ y := by
    intro y
    have hy' : herm σ w₀ (y - herm σ w₀ y • x₀) = 0 := by
      rw [herm_sub_right, herm_smul_right, hx₀, mul_one, sub_self]
    have h1 := hperp _ hy'
    rw [herm_sub_right, herm_smul_right] at h1
    linear_combination h1
  obtain ⟨d, hd⟩ : ∃ d : F, σ d = herm σ (g • x₀ - x₀) x₀ :=
    ⟨σ.symm (herm σ (g • x₀ - x₀) x₀), σ.apply_symm_apply _⟩
  have hmd : g • x₀ - x₀ = d • w₀ := by
    rw [← sub_eq_zero]
    apply eq_zero_of_herm σ
    intro y
    rw [herm_sub_left, herm_smul_left, hd, hm_lin y, sub_self]
  have hfinal : ∀ x : Fin 4 → F, g • x = x + (d * herm σ w₀ x) • w₀ := by
    intro x
    have h := hstep2 x
    rw [hmd, smul_smul] at h
    calc g • x = x + (g • x - x) := by abel
      _ = x + (herm σ w₀ x * d) • w₀ := by rw [h]
      _ = x + (d * herm σ w₀ x) • w₀ := by rw [mul_comm (herm σ w₀ x) d]
  have hxw : herm σ x₀ w₀ = 1 := by
    rw [herm_conj σ hσ.invol w₀ x₀, hx₀, map_one]
  have hsym : σ d = d := by
    have h1 := hN x₀ x₀
    rw [hmd, herm_smul_left, herm_smul_right, hx₀, hxw] at h1
    linear_combination h1
  have hdd : d + σ d = 0 := by
    rw [hsym]
    linear_combination d * h2
  exact ⟨d, hdd, hfinal⟩

end CFSG.LocalAnalysis.RankThreeUC
