module

public import CFSG.ClassicalInvolution.AschTight.S1911Quat

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

section Index2

variable {R V : Subgroup G} (hVR : V ≤ R) (hcard : Nat.card R = 2 * Nat.card V)
include hVR hcard

theorem inv_mul_conj_mem_of_normalizer {b : G} (hbR : b ∈ R) (hbV : b ∉ V) {a : G}
    (haR : a ∈ Subgroup.normalizer (R : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    b⁻¹ * (a * b * a⁻¹) ∈ V := by
  have h1 : a * b * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp haR b).mp hbR
  have h2 : a * b * a⁻¹ ∉ V := fun h => hbV ((Subgroup.mem_normalizer_iff.mp haV b).mpr h)
  exact inv_mul_mem_of_not_mem_of_card_two_mul hVR hcard hbR h1 hbV h2

theorem conj_eq_of_defect (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {b : G} (hbR : b ∈ R)
    (hbV : b ∉ V) {a : G} (haR : a ∈ Subgroup.normalizer (R : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) {u v : G} (hv : v ∈ V)
    (huV : ∀ x ∈ V, u * x = x * u) (hdef : b⁻¹ * (u * b * u⁻¹) = v) (hau : a * u = u * a) :
    a * v * a⁻¹ = v := by
  obtain ⟨c, hc, hcdef⟩ : ∃ c ∈ V, b⁻¹ * (a * b * a⁻¹) = c :=
    ⟨_, inv_mul_conj_mem_of_normalizer hVR hcard hbR hbV haR haV, rfl⟩
  have hab : a * b * a⁻¹ = b * c := by rw [← hcdef]; group
  have hub : u * b * u⁻¹ = b * v := by rw [← hdef]; group
  have hav : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp haV v).mp hv
  have hua : a * u * a⁻¹ = u := by rw [hau]; group
  have h1 : a * (u * b * u⁻¹) * a⁻¹ = u * (a * b * a⁻¹) * u⁻¹ := by
    calc a * (u * b * u⁻¹) * a⁻¹ = (a * u * a⁻¹) * (a * b * a⁻¹) * (a * u * a⁻¹)⁻¹ := by group
      _ = u * (a * b * a⁻¹) * u⁻¹ := by rw [hua]
  rw [hub, hab] at h1
  have h2 : a * (b * v) * a⁻¹ = (a * b * a⁻¹) * (a * v * a⁻¹) := by group
  have h3 : u * (b * c) * u⁻¹ = (u * b * u⁻¹) * (u * c * u⁻¹) := by group
  have huc : u * c * u⁻¹ = c := by rw [huV c hc]; group
  rw [h2, hab, h3, hub, huc] at h1
  have h4 : c * (a * v * a⁻¹) = v * c := by
    have h5 : b * (c * (a * v * a⁻¹)) = b * (v * c) := by
      simp only [mul_assoc] at h1 ⊢
      exact h1
    exact mul_left_cancel h5
  rw [hVc v hv c hc] at h4
  exact mul_left_cancel h4

theorem mem_centralizer_of_defect_eq {b : G} (hbR : b ∈ R) (hbV : b ∉ V) {e₁ e₂ : G}
    (h₂R : e₂ ∈ Subgroup.normalizer (R : Set G)) (h₁V : ∀ x ∈ V, e₁ * x = x * e₁)
    (h₂V : ∀ x ∈ V, e₂ * x = x * e₂)
    (hdef : b⁻¹ * (e₁ * b * e₁⁻¹) = b⁻¹ * (e₂ * b * e₂⁻¹)) :
    e₁ * e₂⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
  have h₂V' : ∀ x ∈ V, e₂⁻¹ * x = x * e₂⁻¹ := by
    intro x hx
    have := h₂V x hx
    calc e₂⁻¹ * x = e₂⁻¹ * (x * e₂) * e₂⁻¹ := by group
      _ = e₂⁻¹ * (e₂ * x) * e₂⁻¹ := by rw [this]
      _ = x * e₂⁻¹ := by group
  have hm := inv_mul_conj_mul hVR hcard hbR (Subgroup.inv_mem _ h₂R) h₁V h₂V'
  have hm2 := inv_mul_conj_mul hVR hcard hbR (Subgroup.inv_mem _ h₂R) h₂V h₂V'
  rw [mul_inv_cancel, one_mul, inv_one, mul_one, inv_mul_cancel] at hm2
  rw [hdef, ← hm2] at hm
  refine mem_centralizer_of_comm hVR hcard hbR hbV (fun x hx => ?_) ?_
  · rw [mul_assoc, h₂V' x hx, ← mul_assoc, h₁V x hx, mul_assoc]
  · have e : e₁ * e₂⁻¹ * b * (e₁ * e₂⁻¹)⁻¹ = b := by
      calc e₁ * e₂⁻¹ * b * (e₁ * e₂⁻¹)⁻¹ = b * (b⁻¹ * (e₁ * e₂⁻¹ * b * (e₁ * e₂⁻¹)⁻¹)) := by
            group
        _ = b := by rw [hm, mul_one]
    calc e₁ * e₂⁻¹ * b = e₁ * e₂⁻¹ * b * (e₁ * e₂⁻¹)⁻¹ * (e₁ * e₂⁻¹) := by group
      _ = b * (e₁ * e₂⁻¹) := by rw [e]

end Index2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
