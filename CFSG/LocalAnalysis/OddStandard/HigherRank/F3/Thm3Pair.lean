module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Three

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit
open CFSG.GH74.GLS.TwoThin

theorem exists_involution_pair {Q : Type} [Group Q] {Y₀ Y₁ : Subgroup Q}
    (hcomm : ∀ a ∈ Y₀, ∀ b ∈ Y₁, a * b = b * a) (hI : Y₀ ⊓ Y₁ = ⊥) {c : Q} (hc2 : c * c = 1)
    (hcc : ∀ y : Q, y * c = c * y) (hc : c ∈ Y₀ ⊔ Y₁) :
    ∃ a ∈ Y₀, ∃ b ∈ Y₁, a * b = c ∧ a * a = 1 ∧ b * b = 1 ∧
      (∀ y ∈ Y₀, y * a = a * y) ∧ (∀ y ∈ Y₁, y * b = b * y) := by
  obtain ⟨a, ha, b, hb, hab⟩ := T23.mem_sup_of_commute hcomm hc
  have haZ : ∀ y ∈ Y₀, y * a = a * y := by
    intro y hy
    have h1 := hcc y
    rw [← hab] at h1
    have h2 : y * a * b = a * y * b := by
      rw [mul_assoc, h1, mul_assoc, mul_assoc, hcomm y hy b hb]
    exact mul_right_cancel h2
  have hbZ : ∀ y ∈ Y₁, y * b = b * y := by
    intro y hy
    have h1 := hcc y
    rw [← hab] at h1
    have h2 : a * (y * b) = a * (b * y) :=
      calc a * (y * b) = a * y * b := (mul_assoc _ _ _).symm
        _ = y * a * b := by rw [hcomm a ha y hy]
        _ = y * (a * b) := mul_assoc _ _ _
        _ = a * b * y := h1
        _ = a * (b * y) := mul_assoc _ _ _
    exact mul_left_cancel h2
  have haa_bb : a * a * (b * b) = 1 := by
    have h1 : (a * b) * (a * b) = 1 := by
      rw [hab]; exact hc2
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hcomm a ha b hb]
      _ = (a * b) * (a * b) := by group
      _ = 1 := h1
  have haa : a * a = 1 := by
    have haa_eq : a * a = (b * b)⁻¹ := mul_eq_one_iff_eq_inv.mp haa_bb
    have hmemY₁ : a * a ∈ Y₁ := by
      rw [haa_eq]
      exact Y₁.inv_mem (Y₁.mul_mem hb hb)
    have hmem : a * a ∈ Y₀ ⊓ Y₁ := ⟨Y₀.mul_mem ha ha, hmemY₁⟩
    rw [hI] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hbb : b * b = 1 := by
    have h := haa_bb
    rw [haa, one_mul] at h
    exact h
  exact ⟨a, ha, b, hb, hab, haa, hbb, haZ, hbZ⟩

theorem exists_involution_over {H : Type} [Group H] [Finite H] {z : H} (hzc : z ∈ center H)
    (hzz : z * z = 1) {K₀ K₁ : Subgroup H} (hK₀ : IsTwoComponent K₀) (hK₁ : IsTwoComponent K₁)
    (hY₀₁ : K₀.map (barMk H) ≠ K₁.map (barMk H))
    (hI : K₀.map (barMk H) ⊓ K₁.map (barMk H) = ⊥) (hz : z ∈ K₀ ⊔ K₁) (hz₀ : z ∉ K₀)
    (hz₁ : z ∉ K₁) :
    ∃ k : H, k * k = 1 ∧ k ≠ 1 ∧ k ≠ z ∧ z * k ≠ 1 ∧ barMk H k ∈ K₀.map (barMk H) ∧
      (∀ y ∈ K₀.map (barMk H), y * barMk H k = barMk H k * y) ∧
      barMk H (z * k) ∈ K₁.map (barMk H) ∧
      (∀ y ∈ K₁.map (barMk H), y * barMk H (z * k) = barMk H (z * k) * y) := by
  set Y₀ : Subgroup (barQ H) := K₀.map (barMk H) with hY₀def
  set Y₁ : Subgroup (barQ H) := K₁.map (barMk H) with hY₁def
  have hY₀c : IsComponent Y₀ :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀)
  have hY₁c : IsComponent Y₁ :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₁).mp hK₁)
  have hcomm : ∀ a ∈ Y₀, ∀ b ∈ Y₁, a * b = b * a := by
    rcases LocalCores.distinct_components_commute hY₀c hY₁c with h | h
    · exact absurd h (by simpa only [hY₀def, hY₁def] using hY₀₁)
    · intro a ha b hb
      have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha
      exact (mem_centralizer_iff.mp h1 b hb).symm
  have hI' : Y₀ ⊓ Y₁ = ⊥ := by simpa only [← hY₀def, ← hY₁def] using hI
  have hc2 : barMk H z * barMk H z = 1 := by rw [← map_mul, hzz, map_one]
  have hcc : ∀ y : barQ H, y * barMk H z = barMk H z * y := by
    intro y
    obtain ⟨m, rfl⟩ := barMk_surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact mem_center_iff.mp hzc m
  have hzY : barMk H z ∈ Y₀ ⊔ Y₁ := by
    have h1 : barMk H z ∈ (K₀ ⊔ K₁).map (barMk H) := ⟨z, hz, rfl⟩
    rwa [Subgroup.map_sup, ← hY₀def, ← hY₁def] at h1
  obtain ⟨a, ha, b, hb, hab, haa, hbb, haZ, hbZ⟩ :=
    exists_involution_pair hcomm hI' hc2 hcc hzY
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hab
    exact hz₁ (T23.mem_of_mk_mem hK₁ (by simpa only [← hY₁def] using (hab ▸ hb)) hzz)
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact hz₀ (T23.mem_of_mk_mem hK₀ (by simpa only [← hY₀def] using (hab ▸ ha)) hzz)
  obtain ⟨k, hkk, hk1, hka⟩ := T23.exists_involution_lift (H := H) haa ha1
  have hka' : barMk H k = a := hka
  have hzk : barMk H (z * k) = b := by
    rw [map_mul, hka', ← hab, mul_assoc, ← hcomm a ha b hb, ← mul_assoc, haa, one_mul]
  refine ⟨k, hkk, hk1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    rw [hka'] at hab
    exact hb1 (mul_left_cancel (by rw [mul_one]; exact hab))
  · intro h
    apply hb1
    rw [← hzk, h, map_one]
  · simpa only [hka', ← hY₀def] using ha
  · intro y hy
    simpa only [hka', ← hY₀def] using haZ y (by simpa only [← hY₀def] using hy)
  · simpa only [hzk, ← hY₁def] using hb
  · intro y hy
    simpa only [hzk, ← hY₁def] using hbZ y (by simpa only [← hY₁def] using hy)

end CFSG.OddStandard.HigherRank.F3
