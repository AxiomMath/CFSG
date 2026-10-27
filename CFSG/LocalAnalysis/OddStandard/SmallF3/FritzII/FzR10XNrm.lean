module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G]

private theorem fzrAux_conj_step {g tau m : G} (hgtau : g * tau * g⁻¹ = m * tau) (k : ℕ)
    (N : G) (hN : g ^ k * tau * (g ^ k)⁻¹ = N * tau) :
    g ^ (k + 1) * tau * (g ^ (k + 1))⁻¹ = (g * N * g⁻¹ * m) * tau := by
  calc g ^ (k + 1) * tau * (g ^ (k + 1))⁻¹
      = g * (g ^ k * tau * (g ^ k)⁻¹) * g⁻¹ := by group
    _ = g * (N * tau) * g⁻¹ := by rw [hN]
    _ = (g * N * g⁻¹) * (g * tau * g⁻¹) := by group
    _ = (g * N * g⁻¹ * m) * tau := by rw [hgtau]; group

theorem fzx_norm4 {g tau m : G} {W : Subgroup G} (htau : ∀ w ∈ W, tau * w * tau⁻¹ = w⁻¹)
    (hgtau : g * tau * g⁻¹ = m * tau) (ha : g ^ 4 ∈ W) :
    (g ^ 3 * m * (g ^ 3)⁻¹) * (g ^ 2 * m * (g ^ 2)⁻¹) * (g * m * g⁻¹) * m = (g ^ 4) ^ 2 := by
  have h1 : g ^ 1 * tau * (g ^ 1)⁻¹ = m * tau := by simpa using hgtau
  have h2 := fzrAux_conj_step hgtau 1 m h1
  have h3 := fzrAux_conj_step hgtau 2 _ h2
  have h4 := fzrAux_conj_step hgtau 3 _ h3
  have hinv := htau (g ^ 4)⁻¹ (W.inv_mem ha)
  have hA : g ^ 4 * tau * (g ^ 4)⁻¹ = (g ^ 4) ^ 2 * tau := by
    calc g ^ 4 * tau * (g ^ 4)⁻¹ = g ^ 4 * (tau * (g ^ 4)⁻¹ * tau⁻¹) * tau := by group
      _ = (g ^ 4) ^ 2 * tau := by rw [hinv]; group
  have h5 := mul_right_cancel (h4.symm.trans hA)
  rw [← h5]
  simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  group

end CFSG.OddStandard.SmallF3.FritzII
