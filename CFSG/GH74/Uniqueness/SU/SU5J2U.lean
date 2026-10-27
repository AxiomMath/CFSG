module

public import CFSG.GH74.Uniqueness.SU.SU5J2R
public import CFSG.GH74.Uniqueness.SU.SU5J2Sub

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

namespace J2Syl

theorem mem_R_of_sq : ∀ s : J2Syl, s.right ≠ 1 → (s * s = 1 ∨ s * s = z0) → s ∈ R := by
  decide +kernel

theorem mem_R_criterion : ∀ y n : J2Syl, y.right ≠ 1 → (y * y = 1 ∨ y * y = z0) → n.right = 1 →
    (n * n = 1 ∨ n * n = z0) → ((n * y) * (n * y) = 1 ∨ (n * y) * (n * y) = z0) → n ∈ R := by
  decide +kernel

theorem U_central : ∀ u m : J2Syl, u ∈ U → m ∈ W → u * m = m * u := by decide +kernel

theorem unique_R (N : Subgroup J2Syl) (hN : N.Normal) (h : IsQ8D8 N) : N = R := by
  obtain ⟨hcard, ζ, hζN, hζ1, hcen, hsq⟩ := h.facts
  have hζc : ∀ m ∈ N, ζ * m = m * ζ := (hcen ζ hζN).2 (Or.inr rfl)
  have hζz : ζ = z0 := by
    have h1 : ∀ g : J2Syl, g * ζ = ζ * g := by
      intro g
      have hconj : g * ζ * g⁻¹ ∈ N := hN.conj_mem ζ hζN g
      have hcentral : ∀ m ∈ N, g * ζ * g⁻¹ * m = m * (g * ζ * g⁻¹) := by
        intro m hm
        have hm' : g⁻¹ * m * g ∈ N := by
          have := hN.conj_mem m hm g⁻¹
          simpa using this
        have h3 := hζc _ hm'
        calc g * ζ * g⁻¹ * m = g * (ζ * (g⁻¹ * m * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * m * g) * ζ) * g⁻¹ := by rw [h3]
          _ = m * (g * ζ * g⁻¹) := by group
      rcases (hcen _ hconj).1 hcentral with h2 | h2
      · exfalso
        apply hζ1
        calc ζ = g⁻¹ * (g * ζ * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      · calc g * ζ = (g * ζ * g⁻¹) * g := by group
          _ = ζ * g := by rw [h2]
    rcases (center_iff ζ).1 (fun t => (h1 t).symm) with h | h
    · exact absurd h hζ1
    · exact h
  have hsq' : ∀ m ∈ N, m * m = 1 ∨ m * m = z0 := fun m hm => by
    rcases hsq m hm with h | h
    · exact Or.inl h
    · exact Or.inr (hζz ▸ h)
  have hNW : ¬ N ≤ W := by
    intro hNW
    have hrel : (N.subgroupOf W).index = 2 := by
      have hW2 : W.index = 2 := by
        have h3 := Subgroup.card_mul_index W
        rw [card_W, card_J2Syl] at h3
        omega
      have hN4 : N.index = 4 := by
        have h2 := Subgroup.card_mul_index N
        rw [hcard, card_J2Syl] at h2
        omega
      have h1 : (N.subgroupOf W).index * W.index = N.index := Subgroup.relIndex_mul_index hNW
      rw [hW2, hN4] at h1
      omega
    have hsqW : ∀ w ∈ W, w * w ∈ N := by
      intro w hw
      have := Subgroup.mul_self_mem_of_index_two hrel ⟨w, hw⟩
      exact Subgroup.mem_subgroupOf.1 this
    have hu0 : (⟨⟨0, 0, F4c.w⟩, 1⟩ : J2Syl) ∈ N := by
      have h1 := hsqW ⟨⟨1, F4c.w, 0⟩, 1⟩ rfl
      have h2 : (⟨⟨1, F4c.w, 0⟩, 1⟩ : J2Syl) * ⟨⟨1, F4c.w, 0⟩, 1⟩ = ⟨⟨0, 0, F4c.w⟩, 1⟩ := by
        decide +kernel
      rwa [h2] at h1
    have hcentral : ∀ m ∈ N, (⟨⟨0, 0, F4c.w⟩, 1⟩ : J2Syl) * m = m * ⟨⟨0, 0, F4c.w⟩, 1⟩ :=
      fun m hm => U_central _ m ⟨rfl, rfl, rfl⟩ (hNW hm)
    have h4 := (hcen _ hu0).1 hcentral
    rw [hζz] at h4
    have hne1 : (⟨⟨0, 0, F4c.w⟩, 1⟩ : J2Syl) ≠ 1 := by decide +kernel
    have hne2 : (⟨⟨0, 0, F4c.w⟩, 1⟩ : J2Syl) ≠ z0 := by decide +kernel
    rcases h4 with h4 | h4
    · exact hne1 h4
    · exact hne2 h4
  have hle : N ≤ R := by
    obtain ⟨y, hyN, hyW⟩ := IsConcreteLE.not_le_iff_exists.1 hNW
    intro n hn
    by_cases hnW : n ∈ W
    · exact mem_R_criterion y n hyW (hsq' y hyN) hnW (hsq' n hn)
        (hsq' (n * y) (N.mul_mem hn hyN))
    · exact mem_R_of_sq n hnW (hsq' n hn)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_R])

theorem z0_mem_R : z0 ∈ R := by decide +kernel

theorem invol_R : ∀ s : J2Syl, (s ∈ R ∧ s ≠ 1 ∧ s * s = 1) ↔
    ((s ∈ U ∧ s ≠ 1) ∨ (s ∉ W ∧ s * s = 1)) := by decide +kernel

theorem mem_R_of_sq_eq_z : ∀ s : J2Syl, s * s = z0 → s ∈ R := by decide +kernel

theorem sq_eq_z_of_mem_R : ∀ s : J2Syl, s ∈ R → s * s ≠ 1 → (s * s) * (s * s) = 1 →
    s * s = z0 := by decide +kernel

theorem A_inf_R : A ⊓ R = U := by
  have h : ∀ s : J2Syl, (s ∈ A ∧ s ∈ R) ↔ s ∈ U := by decide +kernel
  ext s
  rw [Subgroup.mem_inf]
  exact h s

theorem B_inf_R : B ⊓ R = U := by
  have h : ∀ s : J2Syl, (s ∈ B ∧ s ∈ R) ↔ s ∈ U := by decide +kernel
  ext s
  rw [Subgroup.mem_inf]
  exact h s

theorem card_invol_not_W : (Finset.univ.filter (fun s : J2Syl => s ∉ W ∧ s * s = 1)).card = 8 := by
  decide +kernel

end J2Syl

end CFSG.GH74.Uniqueness.SU.SU5
