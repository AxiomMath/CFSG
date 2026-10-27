module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec8t84t_gi_index_two {H : Type} [Group H] [Finite H] (G A : Subgroup H) (hGA : G ≤ A)
    (hcard : Nat.card H = 4 * Nat.card G) (hA : A ≠ ⊤) {z : H} (hzA : z ∈ A) (hzG : z ∉ G) :
    ∀ g ∈ A, g ∈ G ∨ g * z⁻¹ ∈ G := by
  have hGcard : Nat.card G ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, G.one_mem⟩, inferInstance⟩
  have hGindex : G.index = 4 := by
    have h := G.card_mul_index
    rw [hcard, Nat.mul_comm 4 (Nat.card G)] at h
    exact mul_left_cancel₀ hGcard h
  have hdvdA : A.index ∣ 4 := by
    have h := Subgroup.index_dvd_of_le hGA
    rwa [hGindex] at h
  have hAne1 : A.index ≠ 1 := fun h => hA (Subgroup.index_eq_one.mp h)
  have hAi0 : 0 < A.index := Nat.pos_of_dvd_of_pos hdvdA (by decide)
  have hAge : 2 ≤ A.index := by omega
  have hAle : A.index ≤ 4 := Nat.le_of_dvd (by decide) hdvdA
  have hrA : G.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_index hGA
    rw [hGindex] at h
    have hcases : A.index = 2 ∨ A.index = 3 ∨ A.index = 4 := by omega
    rcases hcases with h2 | h3 | h4
    · rw [h2] at h; omega
    · rw [h3] at h; omega
    · exfalso
      rw [h4] at h
      have h1 : G.relIndex A = 1 := by
        have h' : G.relIndex A * 4 = 1 * 4 := by rw [h]
        exact mul_right_cancel₀ (by decide : (4 : Nat) ≠ 0) h'
      have hAG : A ≤ G := Subgroup.relIndex_eq_one.mp h1
      exact hzG ((le_antisymm hGA hAG).symm ▸ hzA)
  obtain ⟨a, haA, ha⟩ := (Subgroup.relIndex_eq_two_iff).mp hrA
  intro g hgA
  by_cases hgG : g ∈ G
  · exact Or.inl hgG
  · right
    have hga : g * a ∈ G := by
      rcases ha g hgA with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hgG
    have hza : z * a ∈ G := by
      rcases ha z hzA with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hzG
    have heq : g * z⁻¹ = (g * a) * (z * a)⁻¹ := by
      simp [mul_inv_rev]
    rw [heq]
    exact mul_mem hga (inv_mem hza)

end CFSG.OddStandard.SmallF3.Omega
