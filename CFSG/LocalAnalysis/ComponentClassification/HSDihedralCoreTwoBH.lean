module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBT

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

omit [Finite X] in
theorem t_ne_dz : Δ.t ≠ Δ.dz := fun h => Δ.t_not_mem_D (h ▸ Δ.dz_mem)

theorem tz_ne_one : Δ.t * Δ.dz ≠ 1 := fun h => Δ.t_ne_dz (by
  rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right (by rw [← pow_two, Δ.dz_sq])])

namespace TwoBSplit

variable {φ : Δ.Fusion} (B : TwoBSplit φ)

theorem eq_of_central_T₁ {u : X} (hu : u ∈ B.T₁) (huc : ∀ g ∈ B.T₁, u * g = g * u) :
    u = 1 ∨ u = Δ.t * Δ.dz := by
  have huS : u ∈ Δ.S := Δ.mem_S_of_commute_t φ.isPGroup φ.le (B.T₁_le hu)
    (huc _ (B.S_T₁ Δ.t_mem))
  have hconj : ∀ g ∈ B.T₁, g * u * g⁻¹ = u := fun g hg => by rw [← huc g hg]; group
  obtain ⟨a, ha, b, hb, rfl⟩ := B.decomp _ huS
  have haz := B.central_left ha hb fun g hg => Or.inl (hconj g (B.S_T₁ (Δ.D_le hg)))
  have hbz := B.central_right ha hb fun g hg =>
    Or.inl (hconj _ (B.S_T₁ (φ.conj_mem g (Δ.D_le hg))))
  have he := hconj _ B.e_T₁
  rcases B.eq_of_central_parts haz hbz with h | h | h | h
  · exact Or.inl h
  · rw [h, B.conj_e_t] at he
    exact absurd he.symm Δ.t_ne_dz
  · rw [h, B.conj_e_dz] at he
    exact absurd he Δ.t_ne_dz
  · exact Or.inr h

theorem eq_of_comm_T₁ {u : X} (hu : u ∈ B.T₁) (hu1 : u ≠ 1) (hutz : u ≠ Δ.t * Δ.dz)
    (hc : ∀ g ∈ B.T₁, g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u * (Δ.t * Δ.dz)) :
    u = Δ.t ∨ u = Δ.dz := by
  rcases B.mem_T₁ hu with huS | hue
  · obtain ⟨a, ha, b, hb, rfl⟩ := B.decomp _ huS
    have haz := B.central_left ha hb fun g hg => hc g (B.S_T₁ (Δ.D_le hg))
    have hbz := B.central_right ha hb fun g hg => hc _ (B.S_T₁ (φ.conj_mem g (Δ.D_le hg)))
    rcases B.eq_of_central_parts haz hbz with h | h | h | h
    · exact absurd h hu1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hutz
  · exfalso
    set s := u * B.e
    have hus : u = s * B.e := B.eq_mul_e
    have hsdb : s⁻¹ * Δ.db * s ∈ Δ.D := by
      simpa using Δ.conj_mem_D _ (inv_mem hue) _ Δ.db_mem
    set c := B.d₀⁻¹ * (s⁻¹ * Δ.db * s) * B.d₀
    have hcD : c ∈ Δ.D := by
      simpa [c] using Δ.conj_mem_D _ (inv_mem B.d₀S) _ hsdb
    have huc : u⁻¹ * Δ.db * u = φ.x * c * φ.x⁻¹ := by
      calc u⁻¹ * Δ.db * u = B.e * (s⁻¹ * Δ.db * s) * B.e⁻¹ := by
            rw [hus, mul_inv_rev, B.e_inv]; group
        _ = φ.x * c * φ.x⁻¹ := B.conj_e_D _
    rcases hc _ (B.S_T₁ (Δ.D_le Δ.db_mem)) with h | h
    · have h' : u⁻¹ * Δ.db * u = Δ.db := by
        calc u⁻¹ * Δ.db * u = u⁻¹ * (Δ.db * u * Δ.db⁻¹) * Δ.db := by group
          _ = Δ.db := by rw [h]; group
      rw [huc] at h'
      have := (B.uniq (one_mem _) Δ.db_mem hcD (one_mem _)
        (by rw [one_mul, h']; group)).1
      exact Δ.db_ne_one this.symm
    · have h' : u⁻¹ * Δ.db * u = (Δ.dz * Δ.db) * (φ.x * Δ.dz * φ.x⁻¹) := by
        calc u⁻¹ * Δ.db * u = u⁻¹ * (Δ.db * u * Δ.db⁻¹) * Δ.db := by group
          _ = Δ.t * Δ.dz * Δ.db := by rw [h]; group
          _ = (Δ.dz * Δ.db) * (φ.x * Δ.dz * φ.x⁻¹) := by
              rw [B.conj_dz, mul_assoc, ← Δ.commute_t (mul_mem (Δ.D_le Δ.dz_mem)
                (Δ.D_le Δ.db_mem))]
      rw [huc] at h'
      have := (B.uniq (one_mem _) (mul_mem Δ.dz_mem Δ.db_mem) hcD Δ.dz_mem
        (by rw [one_mul, h'])).1
      apply Δ.db_ne_dz
      calc Δ.db = Δ.dz⁻¹ * (Δ.dz * Δ.db) := by group
        _ = Δ.dz := by
            rw [← this, mul_one, inv_eq_of_mul_eq_one_right (by rw [← pow_two, Δ.dz_sq])]

end TwoBSplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
