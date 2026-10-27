module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Phi

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {y : G}
    (hy : y ∈ e4Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h1 : f3phi s (y * y⁻¹) = f3phi s y * f3phi s y⁻¹ :=
    y56_phi_mul hH y hy y⁻¹ ((e4Y s).inv_mem hy)
  rw [mul_inv_cancel] at h1
  have h2 : f3phi s (1 : G) = 1 := by simp [f3phi]
  rw [h2] at h1
  calc f3phi s y⁻¹ = 1 * f3phi s y⁻¹ := by rw [one_mul]
    _ = ((f3phi s y)⁻¹ * f3phi s y) * f3phi s y⁻¹ := by rw [inv_mul_cancel]
    _ = (f3phi s y)⁻¹ * (f3phi s y * f3phi s y⁻¹) := by group
    _ = (f3phi s y)⁻¹ * 1 := by rw [← h1]
    _ = (f3phi s y)⁻¹ := by rw [mul_one]

theorem y56_Y_cover (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {y₀ : G} (hy₀ : IsY0 c.s y₀) :
    ∀ y ∈ e4Y c.s, y ∈ e4X0 c.s ∨ (∃ x ∈ e4X0 c.s, y = c.d * x) ∨
      ∃ n ∈ normIn L c.s.fr.E, ∃ x ∈ e4X0 c.s, y = n * y₀ * n⁻¹ * x := by
  intro y hy
  have hfE : f3phi c.s y ∈ c.s.fr.E := y56_phi_mem hH y hy
  by_cases hf1 : f3phi c.s y = 1
  · exact Or.inl ((y56_phi_eq_one hH y hy).mp hf1)
  · by_cases hfz : f3phi c.s y = c.s.fr.z
    · have hdY : c.d ∈ e4Y c.s := y56_d_mem_Y c hH
      have hdY' : c.d⁻¹ ∈ e4Y c.s := (e4Y c.s).inv_mem hdY
      have hxY : c.d⁻¹ * y ∈ e4Y c.s := (e4Y c.s).mul_mem hdY' hy
      have hxphi : f3phi c.s (c.d⁻¹ * y) = 1 := by
        rw [y56_phi_mul hH c.d⁻¹ hdY' y hy, phi_inv hH hdY, y56_phi_d c hH, hfz]
        exact inv_mul_cancel _
      exact Or.inr (Or.inl ⟨c.d⁻¹ * y, (y56_phi_eq_one hH _ hxY).mp hxphi, by group⟩)
    · obtain ⟨hv0V, -, hv0ne1, -, hv0nez, -⟩ := y56_v0 hH
      obtain ⟨n, hn, hnz⟩ :=
        y56_NE_trans hH (y56v0 c.s) (y56_V_le_E hH hv0V) hv0ne1 hv0nez
          (f3phi c.s y) hfE hf1 hfz
      have hnN : n ∈ e4N c.s := y56_NL_le_N hH hn
      have hy'Y : n * y₀ * n⁻¹ ∈ e4Y c.s :=
        y56_N_norm_Y hH n hnN y₀ (y56_y0_mem_Y hH hy₀)
      have hy'inv : (n * y₀ * n⁻¹)⁻¹ ∈ e4Y c.s := (e4Y c.s).inv_mem hy'Y
      have hphi_y' : f3phi c.s (n * y₀ * n⁻¹) = f3phi c.s y := by
        rw [y56_phi_conj hH n hnN y₀, y56_phi_y0 hy₀]
        exact hnz
      have hxY : (n * y₀ * n⁻¹)⁻¹ * y ∈ e4Y c.s := (e4Y c.s).mul_mem hy'inv hy
      have hxphi : f3phi c.s ((n * y₀ * n⁻¹)⁻¹ * y) = 1 := by
        rw [y56_phi_mul hH _ hy'inv y hy, phi_inv hH hy'Y, hphi_y']
        exact inv_mul_cancel _
      exact Or.inr (Or.inr ⟨n, hn, (n * y₀ * n⁻¹)⁻¹ * y,
        (y56_phi_eq_one hH _ hxY).mp hxphi, by group⟩)

end CFSG.OddStandard.HigherRank.YamadaG23
