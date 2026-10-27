module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFacts

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.U33
  CFSG.OddStandard.SmallF3.HarrisU33 CFSG.OddStandard.SmallF3.HarrisU33.K28

private theorem exists_w : ∃ p : Fin 4 × Fin 4 × Fin 2,
    (fg3 * ((fx₁ ^ p.1.val * fx₂ ^ p.2.1.val * flam ^ p.2.2.val) * fg3 *
      (fx₁ ^ p.1.val * fx₂ ^ p.2.1.val * flam ^ p.2.2.val)⁻¹)) ^ 2 = fz := by
  decide +kernel

private theorem fz_comm_gens :
    fx₁ * fz = fz * fx₁ ∧ fx₂ * fz = fz * fx₂ ∧ flam * fz = fz * flam := by
  decide +kernel

private theorem fz_sq_ne : fz * fz = 1 ∧ fz ≠ 1 := by decide +kernel

private theorem not_two_dvd_orderOf_of_pow_three {M : Type*} [Monoid M] {x : M} (h : x ^ 3 = 1) :
    ¬ 2 ∣ orderOf x := fun h2 => by
  have := h2.trans (orderOf_dvd_of_pow_eq_one h)
  omega

variable
  {K : Type} [Group K]

theorem exists_odd_pair_of_psu33 (h : LieModel K .PSU 3 3 1) {g : K} (hg : g * g = 1)
    (hg1 : g ≠ 1) :
    ∃ a b : K, a * g = g * a ∧ b * g = g * b ∧ ¬ 2 ∣ orderOf a ∧ ¬ 2 ∣ orderOf b ∧
      (a * b) ^ 2 = g := by
  obtain ⟨m⟩ := exists_model28 h
  obtain ⟨p, hp⟩ := exists_w
  obtain ⟨hc1, hc2, hc3⟩ := fz_comm_gens
  set w : Pm := fx₁ ^ p.1.val * fx₂ ^ p.2.1.val * flam ^ p.2.2.val with hw_def
  have hw_mem : w ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ fx₁_mem _)
      (Subgroup.pow_mem _ fx₂_mem _)) (Subgroup.pow_mem _ flam_mem _)
  have hw_comm : Commute w fz :=
    ((Commute.pow_left (show Commute fx₁ fz from hc1) _).mul_left
      (Commute.pow_left (show Commute fx₂ fz from hc2) _)).mul_left
      (Commute.pow_left (show Commute flam fz from hc3) _)
  have hg3_comm : Commute fg3 fz := fg3_pow.2.2
  have hb_comm : Commute (w * fg3 * w⁻¹) fz := (hw_comm.mul_left hg3_comm).mul_left hw_comm.inv_left
  have hfz_mem : fz ∈ QP.originalSubgroup := by
    rw [fz]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ fx₁_mem fx₂_mem) 2
  have hb_mem : w * fg3 * w⁻¹ ∈ QP.originalSubgroup :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hw_mem fg3_mem) (Subgroup.inv_mem _ hw_mem)
  let z₀ : K := m.e.symm ⟨fz, hfz_mem⟩
  let a₀ : K := m.e.symm ⟨fg3, fg3_mem⟩
  let b₀ : K := m.e.symm ⟨w * fg3 * w⁻¹, hb_mem⟩
  have hz : m.ε z₀ = fz := by simp [z₀, Model28.ε]
  have ha : m.ε a₀ = fg3 := by simp [a₀, Model28.ε]
  have hb : m.ε b₀ = w * fg3 * w⁻¹ := by simp [b₀, Model28.ε]
  have hz_self : z₀ * z₀ = 1 :=
    m.ε_injective (by rw [map_mul, map_one, hz]; exact fz_sq_ne.1)
  have hz_ne : z₀ ≠ 1 := fun hh => fz_sq_ne.2 (by rw [← hz, hh, map_one])
  obtain ⟨c, hc⟩ := invol_conj_of_psu33 h hz_self hz_ne hg hg1
  have haz : a₀ * z₀ = z₀ * a₀ :=
    m.ε_injective (by rw [map_mul, map_mul, ha, hz]; exact hg3_comm)
  have hbz : b₀ * z₀ = z₀ * b₀ :=
    m.ε_injective (by rw [map_mul, map_mul, hb, hz]; exact hb_comm)
  have hab : (a₀ * b₀) ^ 2 = z₀ :=
    m.ε_injective (by rw [map_pow, map_mul, ha, hb, hz]; exact hp)
  have ha3 : a₀ ^ 3 = 1 := m.ε_injective (by rw [map_pow, ha, map_one]; exact fg3_pow.1)
  have hb3 : b₀ ^ 3 = 1 :=
    m.ε_injective (by rw [map_pow, hb, map_one, conj_pow, fg3_pow.1]; group)
  refine ⟨c * a₀ * c⁻¹, c * b₀ * c⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hc]
    calc c * a₀ * c⁻¹ * (c * z₀ * c⁻¹) = c * (a₀ * z₀) * c⁻¹ := by group
      _ = c * (z₀ * a₀) * c⁻¹ := by rw [haz]
      _ = c * z₀ * c⁻¹ * (c * a₀ * c⁻¹) := by group
  · rw [← hc]
    calc c * b₀ * c⁻¹ * (c * z₀ * c⁻¹) = c * (b₀ * z₀) * c⁻¹ := by group
      _ = c * (z₀ * b₀) * c⁻¹ := by rw [hbz]
      _ = c * z₀ * c⁻¹ * (c * b₀ * c⁻¹) := by group
  · refine not_two_dvd_orderOf_of_pow_three ?_
    rw [conj_pow, ha3]
    group
  · refine not_two_dvd_orderOf_of_pow_three ?_
    rw [conj_pow, hb3]
    group
  · calc (c * a₀ * c⁻¹ * (c * b₀ * c⁻¹)) ^ 2 = (c * (a₀ * b₀) * c⁻¹) ^ 2 := by group
      _ = c * (a₀ * b₀) ^ 2 * c⁻¹ := conj_pow
      _ = g := by rw [hab, hc]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
