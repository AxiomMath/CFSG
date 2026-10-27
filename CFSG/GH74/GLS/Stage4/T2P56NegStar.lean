module

public import CFSG.GH74.GLS.Stage4.T2P56Star

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem star_local_neg {G : Type} [Group G] [Finite G] {z u y : G} {K₁ K₂ H C₁ : Subgroup G}
    {F₂ : Type} [Field F₂] [Finite F₂]
    (hz1 : z ≠ 1) (hu2 : u * u = 1)
    (hKc : ∀ x ∈ K₁, ∀ x' ∈ K₂, x * x' = x' * x) (hzK₁ : z ∈ K₁) (hzK₂ : z ∈ K₂)
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂)
    (hF₂ : Odd (Nat.card F₂)) (hF₂3 : 3 ≤ Nat.card F₂)
    (hHc : ∀ x ∈ H, ∀ x' ∈ H, x * x' = x' * x) (hzH : z ∈ H) (huH : u ∈ H) (hyH : y ∈ H)
    (hyK₁ : y ∈ K₁)
    (hH₁cent : ∀ y' ∈ H ⊓ K₁, y' * y' ≠ 1 → ∀ d ∈ K₁, d * y' = y' * d → d ∈ H)
    (hy2 : y * y ≠ 1)
    (hoddK₂ : ∀ f : G, f * z = z * f → Odd (orderOf f) → ∀ x ∈ K₂, f * x * f⁻¹ ∈ K₂)
    (hC₁n : ∀ c : G, c * z = z * c → ∀ x ∈ C₁, c * x * c⁻¹ ∈ C₁) (huC₁ : u ∈ C₁)
    (hidx : (K₁ ⊔ K₂).relIndex C₁ = 2) (B : Subgroup G) (hBy : ∀ b ∈ B, b * y = y * b)
    (hBn : ∀ g : G, g * y = y * g → ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hBodd : Odd (Nat.card B)) :
    ∀ b ∈ B, b * z = z * b → b * u = u * b := by
  intro b₀ hb₀ hb₀z
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hzu : z * u = u * z := hHc z hzH u huH
  have huy : u * y = y * u := hHc u huH y hyH
  set d : G := b₀ * u * b₀⁻¹ * u⁻¹ with hd
  have hdB : d ∈ B := by
    have : d = b₀ * (u * b₀⁻¹ * u⁻¹) := by rw [hd]; group
    rw [this]
    exact B.mul_mem hb₀ (hBn u huy _ (B.inv_mem hb₀))
  have hdz : d * z = z * d := by
    have hb : Commute b₀ z := hb₀z
    have hu' : Commute u z := hzu.symm
    exact ((((hb.mul_left hu').mul_left hb.inv_left).mul_left hu'.inv_left)).eq
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hdB)
  have hdinv : u * d * u⁻¹ = d⁻¹ := by
    have e1 : d⁻¹ = u * b₀ * u * b₀⁻¹ := by
      rw [hd, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, hu1]
      group
    rw [e1]
    calc u * d * u⁻¹ = (u * b₀ * u * b₀⁻¹) * (u * u) := by rw [hd, hu1]; group
      _ = u * b₀ * u * b₀⁻¹ := by rw [hu2, mul_one]
  have hdC₁ : d ∈ C₁ := by
    have h1 := hC₁n b₀ hb₀z u huC₁
    exact C₁.mul_mem h1 (C₁.inv_mem huC₁)
  have hdK : d ∈ K₁ ⊔ K₂ := t2C_odd_mem_of_index_two hidx hdC₁ hdodd
  obtain ⟨k₁, hk₁, k₂, hk₂, hdk⟩ := (mem_sup_iff_of_comm hKc d).1 hdK
  have hP₂ : ∀ q, q = Nat.card F₂ → Odd q ∧ 3 ≤ q := fun q hq => by rw [hq]; exact ⟨hF₂, hF₂3⟩
  have hsl₂ : HasSL2Model ↥K₂ (fun q => q = Nat.card F₂) :=
    ⟨F₂, inferInstance, inferInstance, rfl,
      ⟨e₂.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hdK₂ : ∀ k ∈ K₂, d * k = k * d := by
    intro k hk
    have hky : k * y = y * k := (hKc y hyK₁ k hk).symm
    have hdn : d * k * d⁻¹ ∈ K₂ := hoddK₂ d hdz hdodd k hk
    have hcB : k * d⁻¹ * k⁻¹ ∈ B := hBn k hky d⁻¹ (B.inv_mem hdB)
    have hcomm : d * k * d⁻¹ * k⁻¹ ∈ B := by
      have : d * k * d⁻¹ * k⁻¹ = d * (k * d⁻¹ * k⁻¹) := by group
      rw [this]; exact B.mul_mem hdB hcB
    have hcK₂ : d * k * d⁻¹ * k⁻¹ ∈ K₂ := K₂.mul_mem hdn (K₂.inv_mem hk)
    have h1 := eq_one_of_mem_inf_of_sl2' B hBodd (K := K₂) (fun k' hk' n hn =>
      hBn k' ((hKc y hyK₁ k' hk').symm) n hn) hP₂ hsl₂ hcK₂ hcomm
    calc d * k = (d * k * d⁻¹ * k⁻¹) * (k * d) := by group
      _ = k * d := by rw [h1, one_mul]
  have hdK₁ : d ∈ K₁ := by
    have hk₂c : ∀ k ∈ K₂, k₂ * k = k * k₂ := by
      intro k hk
      have h1 := hdK₂ k hk
      rw [hdk] at h1
      have h2 : k₁ * (k₂ * k) = k₁ * (k * k₂) := by
        calc k₁ * (k₂ * k) = k₁ * k₂ * k := by group
          _ = k * (k₁ * k₂) := h1
          _ = (k * k₁) * k₂ := by group
          _ = (k₁ * k) * k₂ := by rw [(hKc k₁ hk₁ k hk)]
          _ = k₁ * (k * k₂) := by group
      exact mul_left_cancel h2
    have hz₂c : ∀ a ∈ K₂, a * z = z * a := fun a ha => (hKc z hzK₁ a ha).symm
    have hcent := (CFSG.GH74.Generic.S3.sl2_img_eq_z (ringChar_ne_two_of_odd hF₂) e₂.symm hzK₂ hz₂c hz1).1
    rcases hcent k₂ hk₂ hk₂c with h | h
    · rw [hdk, h, mul_one]; exact hk₁
    · rw [hdk, h]; exact K₁.mul_mem hk₁ hzK₁
  have hdy : d * y = y * d := hBy d hdB
  have hdH : d ∈ H := hH₁cent y ⟨hyH, hyK₁⟩ hy2 d hdK₁ hdy
  have hdu : d * u = u * d := hHc d hdH u huH
  have hdd : d = d⁻¹ := by
    rw [← hdinv]
    calc d = d * u * u⁻¹ := by group
      _ = u * d * u⁻¹ := by rw [hdu]
  have hdsq : d * d = 1 := by
    calc d * d = d * d⁻¹ := by rw [← hdd]
      _ = 1 := mul_inv_cancel d
  have hd1 : d = 1 := eq_one_of_sq_eq_one_of_odd hBodd hdB hdsq
  calc b₀ * u = d * (u * b₀) := by rw [hd]; group
    _ = u * b₀ := by rw [hd1, one_mul]

end CFSG.GH74.GLS.Stage4.Rest
