module

public import CFSG.ClassicalInvolution.AschTight.S1916WrAut
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem WrData.eq_of_comm {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) {H : Subgroup G}
    (hHP : H ≤ P) (hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hcard : Nat.card B ≤ Nat.card H) :
    H = B := by
  by_contra hne
  obtain ⟨x, hxH, hxB⟩ : ∃ x ∈ H, x ∉ B := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge hcon hcard)
  have hBN : P ≤ Subgroup.normalizer (B : Set G) := by
    rw [h.P_eq]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.bN)
  have hinf : B ⊓ H ≤ Subgroup.zpowers (a * c) := by
    rintro y ⟨hyB, hyH⟩
    have hxb : x * b ∈ B := (h.PB x (hHP hxH)).resolve_left hxB
    have h1 : y * x = x * y := hHab y hyH x hxH
    have h2 : y * (x * b) = (x * b) * y := h.comm y hyB _ hxb
    have h3 : y * b = b * y := by
      have h4 : x * (y * b) = x * (b * y) := by
        calc x * (y * b) = (y * x) * b := by rw [← mul_assoc, ← h1]
          _ = (x * b) * y := by rw [mul_assoc, h2]
          _ = x * (b * y) := by group
      exact mul_left_cancel h4
    refine h.fix hyB ?_
    rw [← h3, mul_assoc, mul_inv_cancel, mul_one]
  have hcardinf : Nat.card ↥(B ⊓ H) ≤ orderOf a :=
    (Subgroup.card_le_of_le hinf).trans (by rw [Nat.card_zpowers, h.ord_ac])
  have h1 := card_sup_mul_card_inf (A := B) (C := H) (hHP.trans hBN)
  have h2 : Nat.card ↥(B ⊔ H) ≤ Nat.card P := Subgroup.card_le_of_le (sup_le h.BP hHP)
  rw [h.card_B] at h1 hcard
  rw [h.card_P] at h2
  have h5 := Nat.mul_le_mul h2 hcardinf
  rw [h1] at h5
  have h4 := h.four
  set n := orderOf a with hn
  have h6 : n * n * (n * n) ≤ n * n * Nat.card H := Nat.mul_le_mul_left _ hcard
  have h7 : 4 * (n * n * n) ≤ n * (n * n * n) := Nat.mul_le_mul_right _ h4
  have h8 : 0 < n * n * n := by positivity
  nlinarith

omit [Finite G] in
theorem WrData.mem_of_comm {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) {u x : G}
    (huB : u ∈ B) (hu : u ∉ Subgroup.zpowers (a * c)) (hxP : x ∈ P) (hxu : x * u = u * x) :
    x ∈ B := by
  by_contra hxB
  have hxb : x * b ∈ B := (h.PB x hxP).resolve_left hxB
  have hbu : b * u * b⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp h.bN u).mp huB
  apply hu
  refine h.fix huB ?_
  have hc := h.comm (x * b) hxb (b * u * b⁻¹) hbu
  have h1 : x * u * x⁻¹ = u := by rw [hxu]; group
  have h2 : (x * b) * (b * u * b⁻¹) * (x * b)⁻¹ = x * (b * b) * u * (b * b)⁻¹ * x⁻¹ := by group
  rw [h.b2] at h2
  calc b * u * b⁻¹ = (x * b) * (b * u * b⁻¹) * (x * b)⁻¹ := by rw [hc]; group
    _ = x * u * x⁻¹ := by rw [h2]; group
    _ = u := h1

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
