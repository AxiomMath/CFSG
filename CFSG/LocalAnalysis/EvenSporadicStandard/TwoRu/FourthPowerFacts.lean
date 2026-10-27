module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.FourthPowers

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open Subgroup

variable {L J : Type*} [Group L] [Group J]

theorem eq_one_or_eq_of_mem_zpowers {t : L} (ht : orderOf t = 2) {c : L} (hc : c ∈ zpowers t) :
    c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul]
    simp [h2]
  · right
    rw [hm, zpow_add, zpow_mul]
    simp [h2]

theorem exists_conj_or_conj_mul_of_ker {q : L →* J} (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) {x y : L} {h : J}
    (hxy : q y = h * q x * h⁻¹) :
    ∃ g : L, y = g * x * g⁻¹ ∨ y = g * x * g⁻¹ * t := by
  obtain ⟨g, rfl⟩ := hq h
  have hc : (g * x * g⁻¹)⁻¹ * y ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hxy, inv_mul_cancel]
  rw [hker] at hc
  refine ⟨g, ?_⟩
  have hy : y = g * x * g⁻¹ * ((g * x * g⁻¹)⁻¹ * y) := by group
  rcases eq_one_or_eq_of_mem_zpowers ht hc with h1 | h1
  · left
    rw [hy, h1, mul_one]
  · right
    rw [hy, h1]

theorem fourthPowerDichotomy_of_facts {q : L →* J} (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) {A : J}
    (Z : Set J) (hB : ∀ (v : L) (h : J), q v = h * A * h⁻¹ → v ^ 2 = t)
    (hNS : ∀ w : J, w ^ 4 = 1 → w ^ 2 ≠ 1 → ∀ h : J, w ^ 2 ≠ h * A * h⁻¹)
    (hdich : ∀ s : J, s ^ 2 = 1 → s ≠ 1 → (∃ h, s = h * A * h⁻¹) ∨ s ∈ Z)
    (hZ : ∀ s ∈ Z, ∀ s' ∈ Z, ∃ h : J, s' = h * s * h⁻¹)
    {a₁ a₂ : L} (h₁ : a₁ ^ 8 = 1) (h₂ : a₂ ^ 8 = 1) (h₁' : a₁ ^ 4 ≠ 1) (h₂' : a₂ ^ 4 ≠ 1)
    (h₁t : a₁ ^ 4 ≠ t) (h₂t : a₂ ^ 4 ≠ t) (hnc : ¬ IsConj (a₁ ^ 4) (a₂ ^ 4)) :
    FourthPowerDichotomy L t := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  have htc : ∀ y : L, y * t = t * y := fun y => mem_center_iff.1 (hcen (mem_zpowers t)) y
  have hkq : ∀ x : L, q x = 1 → x = 1 ∨ x = t := fun x hx =>
    eq_one_or_eq_of_mem_zpowers ht (hker ▸ hx)
  have hqt : q t = 1 := by rw [← MonoidHom.mem_ker, hker]; exact mem_zpowers t
  have hinvol : ∀ v : L, v ^ 2 = 1 → v ≠ 1 → v ≠ t → q v ∈ Z := by
    intro v hv2 hv1 hvt
    have hq2 : (q v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
    have hq1 : q v ≠ 1 := fun h => (hkq v h).elim hv1 hvt
    rcases hdich _ hq2 hq1 with ⟨h, hh⟩ | hz
    · exact absurd ((hB v h hh).symm.trans hv2) ht1
    · exact hz
  have hconj : ∀ v₁ v₂ : L, v₁ ^ 2 = 1 → v₂ ^ 2 = 1 → v₁ ≠ 1 → v₂ ≠ 1 → v₁ ≠ t → v₂ ≠ t →
      ∃ g : L, v₂ = g * v₁ * g⁻¹ ∨ v₂ = g * v₁ * g⁻¹ * t := by
    intro v₁ v₂ hv₁ hv₂ h1 h2 h1t h2t
    obtain ⟨h, hh⟩ := hZ _ (hinvol v₁ hv₁ h1 h1t) _ (hinvol v₂ hv₂ h2 h2t)
    exact exists_conj_or_conj_mul_of_ker hq ht hker hh
  have hx₁ : (a₁ ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h₁
  have hx₂ : (a₂ ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h₂
  have hx₁1 : a₁ ^ 4 ≠ 1 := h₁'
  refine ⟨fun u hu => ?_, fun x hx2 hx1 hxt => ?_⟩
  ·
    have hv2 : (u ^ 2) ^ 2 = t := by rw [← pow_mul]; exact hu
    have hv1 : u ^ 2 ≠ 1 := fun h => ht1 (by rw [← hv2, h, one_pow])
    have hvt : u ^ 2 ≠ t := fun h => ht1 (by
      have := hv2
      rw [h] at this
      rw [← this]
      exact ht2)
    have hq4 : (q u) ^ 4 = 1 := by rw [← map_pow, hu, hqt]
    have hq2 : (q (u ^ 2)) ^ 2 = 1 := by rw [← map_pow, hv2, hqt]
    have hq1 : q (u ^ 2) ≠ 1 := fun h => (hkq _ h).elim hv1 hvt
    rcases hdich _ hq2 hq1 with ⟨h, hh⟩ | hz
    · exact hNS (q u) hq4 (by rw [← map_pow]; exact hq1) h (by rw [← map_pow]; exact hh)
    · obtain ⟨h, hh⟩ := hZ _ (hinvol _ hx₂ h₂' h₂t) _ hz
      obtain ⟨g, hg | hg⟩ := exists_conj_or_conj_mul_of_ker hq ht hker hh
      · apply ht1
        rw [← hv2, hg, conj_pow, hx₂]
        group
      · apply ht1
        have hcomm : Commute (g * a₂ ^ 4 * g⁻¹) t := htc _
        rw [← hv2, hg, hcomm.mul_pow, conj_pow, hx₂, ht2]
        group
  ·
    obtain ⟨g, hg | hg⟩ := hconj _ x hx₂ hx2 h₂' hx1 h₂t hxt
    · exact ⟨g * a₂ * g⁻¹, by rw [conj_pow, hg]⟩
    · obtain ⟨g', hg' | hg'⟩ := hconj _ _ hx₂ hx₁ h₂' h₁' h₂t h₁t
      · exact absurd (IsConj.symm (isConj_iff.2 ⟨g', hg'.symm⟩)) hnc
      · refine ⟨g * g'⁻¹ * a₁ * g' * g⁻¹, ?_⟩
        have hw : g * g'⁻¹ * a₁ * g' * g⁻¹ = (g * g'⁻¹) * a₁ * (g * g'⁻¹)⁻¹ := by group
        rw [hw, conj_pow, hg', hg]
        have e1 : g * g'⁻¹ * (g' * a₂ ^ 4 * g'⁻¹ * t) * (g * g'⁻¹)⁻¹ =
            g * a₂ ^ 4 * g⁻¹ * (g * g'⁻¹ * t * (g * g'⁻¹)⁻¹) := by group
        rw [e1]
        have e2 : g * g'⁻¹ * t * (g * g'⁻¹)⁻¹ = t := by
          rw [htc (g * g'⁻¹), mul_assoc, mul_inv_cancel, mul_one]
        rw [e2]

end CFSG.EvenSporadicStandard.TwoRu
