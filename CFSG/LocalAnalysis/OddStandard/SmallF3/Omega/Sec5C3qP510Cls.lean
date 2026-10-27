module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Alt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510_W5_not_conj (h : Sec510Ctx G t L S z r ρ B A φ) {w : G}
    (hw : w ∈ wclass φ 5) : ¬ ∃ g : G, g⁻¹ * t * g = w := by
  rintro ⟨g, hg⟩
  obtain ⟨a, b, ha, hb, hab, habz, -⟩ := sec5p510_exists_cycle h
  have htt := sec5p510c_t_mul_t h
  have hu : t * w ∈ wclass φ 1 := by
    simpa using sec5p510c_t_mul_mem h (k := 5) (by norm_num) hw
  have htD : t ∈ conjClassIn (normalizer (A : Set G)) t := ⟨1, one_mem _, by group⟩
  have htu : t ≠ t * w := fun heq =>
    Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (6 : ℕ) ≠ 1))
      h.model.t_mem_wclass (heq ▸ hu)
  obtain ⟨m, -, hmt, hmu⟩ := sec5p510c_two_trans h htD (sec5p510c_W1_subset_delta h hu)
    (sec5p510c_W1_subset_delta h ha) (sec5p510c_W1_subset_delta h hb) htu hab
  have htz : t * z = a * b := by
    calc t * z = t * (t * a * b) := by rw [habz]
      _ = t * t * a * b := by group
      _ = a * b := by rw [htt, one_mul]
  have hmw : m * w * m⁻¹ = a * b := by
    have htw : t * (t * w) = w := by rw [← mul_assoc, htt, one_mul]
    calc m * w * m⁻¹ = m * (t * (t * w)) * m⁻¹ := by rw [htw]
      _ = (m * t * m⁻¹) * (m * (t * w) * m⁻¹) := by group
      _ = a * b := by rw [hmt, hmu]
  refine h.nconj ⟨g * m⁻¹, ?_⟩
  calc (g * m⁻¹)⁻¹ * t * (g * m⁻¹) = m * (g⁻¹ * t * g) * m⁻¹ := by group
    _ = m * w * m⁻¹ := by rw [hg]
    _ = t * z := by rw [hmw, htz]

theorem sec5p510_tG_inter_A (h : Sec510Ctx G t L S z r ρ B A φ) {g : G}
    (hg : g⁻¹ * t * g ∈ A) : g⁻¹ * t * g ∈ conjClassIn (normalizer (A : Set G)) t := by
  have hy1 : g⁻¹ * t * g ≠ 1 := by
    intro h1
    have ht1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h2 := h.involution
    rw [ht1, orderOf_one] at h2
    omega
  obtain ⟨k, hk1, hk6, hk⟩ := h.model.perm.exists_wclass_pos hg hy1
  have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.delta]
    exact Or.inr hk
  · exfalso
    obtain ⟨a, -, hay⟩ := h.model.perm.exists_conj h.model.tz_mem_wclass hk
    refine h.nconj ⟨g * a, ?_⟩
    calc (g * a)⁻¹ * t * (g * a) = a⁻¹ * (g⁻¹ * t * g) * a := by group
      _ = a⁻¹ * (a * (t * z) * a⁻¹) * a := by rw [hay]
      _ = t * z := by group
  · exfalso
    have hz : g⁻¹ * t * g ∈ conjClassIn (normalizer (A : Set G)) z := by
      rw [h.zM]
      exact Or.inl hk
    obtain ⟨m, -, hmy⟩ := hz
    refine h.tnz (m⁻¹ * g⁻¹) ?_
    calc (m⁻¹ * g⁻¹)⁻¹ * z * (m⁻¹ * g⁻¹) = g * (m * z * m⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [← hmy]
      _ = t := by group
  · exfalso
    have hz : g⁻¹ * t * g ∈ conjClassIn (normalizer (A : Set G)) z := by
      rw [h.zM]
      exact Or.inr hk
    obtain ⟨m, -, hmy⟩ := hz
    refine h.tnz (m⁻¹ * g⁻¹) ?_
    calc (m⁻¹ * g⁻¹)⁻¹ * z * (m⁻¹ * g⁻¹) = g * (m * z * m⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [← hmy]
      _ = t := by group
  · exact absurd ⟨g, rfl⟩ (sec5p510_W5_not_conj h hk)
  · rw [h.delta]
    exact Or.inl hk

end CFSG.OddStandard.SmallF3.Omega
