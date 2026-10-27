module

public import CFSG.GH74.Uniqueness.Section14Lem47Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace Sec147

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

section Concl

variable (h146 : Concl146 M t n K Mo U T S2)
include h146

theorem commutator_mem_Mo_of_sq (hsq : ∀ x ∈ S2, x * x ∈ Mo) {x y : X} (hx : x ∈ S2)
    (hy : y ∈ S2) : x * y * x⁻¹ * y⁻¹ ∈ Mo := by
  have hxy2 := hsq (x * y) (mul_mem hx hy)
  have hx2 := hsq x hx
  have hy2 := hsq y hy
  have hc : y * (x * x)⁻¹ = (x * x)⁻¹ * y := comm_S2_Mo h146 hy (inv_mem hx2)
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hc]
      _ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxy2 (inv_mem hx2)) (inv_mem hy2)

theorem exists_involution_mul {a : X} (ha : a ∈ S2) (haT : a ∉ T) (ha2 : a * a = 1) {b : X}
    (hb : b ∈ S2) (hbT : b ∉ T) :
    ∃ a' ∈ S2, a' ∉ T ∧ a' * a' = 1 ∧ ∃ t₀ ∈ T, b = a' * t₀ := by
  obtain ⟨k, hk, hkt⟩ := h146.K_trans_S2 a ha haT b hb hbT
  have ha'S : k * a * k⁻¹ ∈ S2 := (mem_normalizer_iff.mp (h146.K_norm_S2 hk) a).mp ha
  have ha'2 : (k * a * k⁻¹) * (k * a * k⁻¹) = 1 := by
    calc (k * a * k⁻¹) * (k * a * k⁻¹) = k * (a * a) * k⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  refine ⟨k * a * k⁻¹, ha'S, ?_, ha'2, (k * a * k⁻¹)⁻¹ * b, hkt, by group⟩
  intro h
  apply hbT
  have h' := mul_mem h hkt
  rwa [mul_inv_cancel_left] at h'

end Concl

section Elem

variable (F : Facts14 Z M t n r L K J Mo P U T S2) (h146 : Concl146 M t n K Mo U T S2)
include F h146

theorem conj_P_eq_mul {a : X} (ha : a ∈ S2) (haT : a ∉ T) (ha2 : a * a = 1) {p₀ : X}
    (hp₀ : p₀ ∈ P) : ∃ z ∈ Mo, a * p₀ * a⁻¹ = p₀ * z := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hinv2 : a⁻¹ * a⁻¹ = 1 := by rw [hinv]; exact ha2
  have hc : a * p₀ * a⁻¹ ∈ T :=
    (mem_normalizer_iff.mp (S2_le_normalizer_T F ha) p₀).mp (P_le_T F hp₀)
  obtain ⟨p', hp', u', hu', hpu⟩ := exists_mul_of_mem_T F hc
  have hsq1 : (a * p₀ * a⁻¹) * (a * p₀ * a⁻¹) = p₀ * p₀ := by
    have e : (a * p₀ * a⁻¹) * (a * p₀ * a⁻¹) = a * (p₀ * p₀) * a⁻¹ := by group
    rw [e, comm_S2_Mo h146 ha (F.P_sq p₀ hp₀)]
    group
  have hsq : p₀ * p₀ = p' * p' := by
    rw [← mul_mul_self_PU F hp' hu', ← hpu, hsq1]
  have hm : p₀⁻¹ * p' ∈ Mo := F.P_sq_inj p₀ hp₀ p' hp' hsq
  have hz : p₀⁻¹ * p' * u' ∈ Mo ⊔ U := mul_mem (mem_sup_left hm) (mem_sup_right hu')
  have hzeq : a * p₀ * a⁻¹ = p₀ * (p₀⁻¹ * p' * u') := by
    rw [hpu]
    group
  generalize p₀⁻¹ * p' * u' = z at hz hzeq
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_Mo_sup_U F hz
  have h1 : a * (a * p₀ * a⁻¹) * a⁻¹ = p₀ := by
    calc a * (a * p₀ * a⁻¹) * a⁻¹ = (a * a) * p₀ * (a⁻¹ * a⁻¹) := by group
      _ = p₀ := by rw [ha2, hinv2]; group
  have h2 : a * (p₀ * z) * a⁻¹ = (a * p₀ * a⁻¹) * (a * z * a⁻¹) := by group
  have h3 : p₀ * (z * (a * z * a⁻¹)) = p₀ * 1 := by
    calc p₀ * (z * (a * z * a⁻¹)) = (p₀ * z) * (a * z * a⁻¹) := by group
      _ = (a * p₀ * a⁻¹) * (a * z * a⁻¹) := by rw [hzeq]
      _ = a * (p₀ * z) * a⁻¹ := h2.symm
      _ = a * (a * p₀ * a⁻¹) * a⁻¹ := by rw [hzeq]
      _ = p₀ * 1 := by rw [h1, mul_one]
  have h4 : z * (a * z * a⁻¹) = 1 := mul_left_cancel h3
  have h5 : a * z * a⁻¹ = z := by
    have := eq_inv_of_mul_eq_one_right h4
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have h6 : a * z = z * a := mul_inv_eq_iff_eq_mul.mp h5
  exact ⟨z, h146.cent_out a ha haT z hz h6, hzeq⟩

theorem commutator_mem_Mo {a : X} (ha : a ∈ S2) (haT : a ∉ T) (ha2 : a * a = 1) :
    ∀ x ∈ T, a * x * a⁻¹ * x⁻¹ ∈ Mo := by
  intro x hx
  obtain ⟨p₀, hp₀, u₀, hu₀, rfl⟩ := exists_mul_of_mem_T F hx
  obtain ⟨z, hz, hzeq⟩ := conj_P_eq_mul F h146 ha haT ha2 hp₀
  have hz₂ := h146.quot_center a ha u₀ (mem_sup_right hu₀)
  have e : a * (p₀ * u₀) * a⁻¹ * (p₀ * u₀)⁻¹ =
      p₀ * (z * (a * u₀ * a⁻¹ * u₀⁻¹)) * p₀⁻¹ := by
    calc a * (p₀ * u₀) * a⁻¹ * (p₀ * u₀)⁻¹
        = (a * p₀ * a⁻¹) * (a * u₀ * a⁻¹ * u₀⁻¹) * p₀⁻¹ := by group
      _ = (p₀ * z) * (a * u₀ * a⁻¹ * u₀⁻¹) * p₀⁻¹ := by rw [hzeq]
      _ = p₀ * (z * (a * u₀ * a⁻¹ * u₀⁻¹)) * p₀⁻¹ := by group
  rw [e, F.Mo_central p₀ hp₀ _ (mul_mem hz hz₂)]
  simpa using mul_mem hz hz₂

theorem mul_self_mem_Mo_of_mem_S2 (hex : ∃ a ∈ S2, a ∉ T ∧ a * a = 1) {x : X} (hx : x ∈ S2) :
    x * x ∈ Mo := by
  by_cases hxT : x ∈ T
  · exact mul_self_mem_Mo_of_mem_T F hxT
  obtain ⟨a, ha, haT, ha2⟩ := hex
  obtain ⟨a', ha'S, ha'T, ha'2, t₀, ht₀, rfl⟩ :=
    exists_involution_mul h146 ha haT ha2 hx hxT
  have hinv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'2
  have hm := commutator_mem_Mo F h146 ha'S ha'T ha'2 t₀ ht₀
  have e : a' * t₀ * (a' * t₀) = (a' * t₀ * a'⁻¹ * t₀⁻¹) * (t₀ * t₀) := by
    rw [hinv]
    group
  rw [e]
  exact mul_mem hm (mul_self_mem_Mo_of_mem_T F ht₀)

theorem elem_of_involution (hex : ∃ a ∈ S2, a ∉ T ∧ a * a = 1) :
    ∀ x ∈ S2, ∀ y ∈ S2, x * y * x⁻¹ * y⁻¹ ∈ Mo ∧ x * x ∈ Mo := fun _ hx _ hy =>
  ⟨commutator_mem_Mo_of_sq h146 (fun _ hz => mul_self_mem_Mo_of_mem_S2 F h146 hex hz) hx hy,
    mul_self_mem_Mo_of_mem_S2 F h146 hex hx⟩

end Elem

end Sec147

end CFSG.GH74.Uniqueness
