module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.RestSetupRank

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section InQ

variable {G : Type} [Group G]

@[expose] def t2InQ (H : Subgroup G) (w₀ x : G) : Prop := x ∈ H ∨ ∃ h ∈ H, x = h * w₀

theorem t2InQ_mul {H : Subgroup G} {w₀ : G} (hw₀2 : w₀ * w₀ = 1)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) {x y : G} (hx : t2InQ H w₀ x) (hy : t2InQ H w₀ y) :
    t2InQ H w₀ (x * y) := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  rcases hx with hx | ⟨a, ha, rfl⟩ <;> rcases hy with hy | ⟨b, hb, rfl⟩
  · exact Or.inl (H.mul_mem hx hy)
  · exact Or.inr ⟨x * b, H.mul_mem hx hb, by group⟩
  · refine Or.inr ⟨a * y⁻¹, H.mul_mem ha (H.inv_mem hy), ?_⟩
    calc a * w₀ * y = a * (w₀ * y * w₀⁻¹) * w₀ := by group
      _ = a * y⁻¹ * w₀ := by rw [hinv y hy]
  · refine Or.inl ?_
    have h1 := hinv b hb
    rw [hw₀] at h1
    have : a * w₀ * (b * w₀) = a * b⁻¹ := by
      calc a * w₀ * (b * w₀) = a * (w₀ * b * w₀) := by group
        _ = a * b⁻¹ := by rw [h1]
    rw [this]
    exact H.mul_mem ha (H.inv_mem hb)

theorem t2InQ_inv {H : Subgroup G} {w₀ : G} (hw₀2 : w₀ * w₀ = 1)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) {x : G} (hx : t2InQ H w₀ x) :
    t2InQ H w₀ x⁻¹ := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  rcases hx with hx | ⟨a, ha, rfl⟩
  · exact Or.inl (H.inv_mem hx)
  · refine Or.inr ⟨a, ha, ?_⟩
    calc (a * w₀)⁻¹ = w₀⁻¹ * a⁻¹ := by group
      _ = w₀ * a⁻¹ := by rw [hw₀]
      _ = (w₀ * a⁻¹ * w₀⁻¹) * w₀ := by group
      _ = a * w₀ := by rw [hinv a⁻¹ (H.inv_mem ha), inv_inv]

theorem t2InQ_conj {H : Subgroup G} {w₀ c : G} (hcH : ∀ h ∈ H, c * h * c⁻¹ ∈ H)
    (hcw : c * w₀ = w₀ * c) {x : G} (hx : t2InQ H w₀ x) : t2InQ H w₀ (c * x * c⁻¹) := by
  rcases hx with hx | ⟨a, ha, rfl⟩
  · exact Or.inl (hcH x hx)
  · refine Or.inr ⟨c * a * c⁻¹, hcH a ha, ?_⟩
    calc c * (a * w₀) * c⁻¹ = c * a * (c⁻¹ * c) * w₀ * c⁻¹ := by group
      _ = c * a * c⁻¹ * (c * w₀ * c⁻¹) := by group
      _ = c * a * c⁻¹ * w₀ := by rw [hcw]; group

end InQ

section Algebra

variable {G : Type} [Group G]

theorem t2P53_a_mem {H : Subgroup G} {a w₁ w₂ w₀ : G} (hw₀def : w₀ = w₁ * w₂)
    (haH : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (ha3 : a * a * a ∈ H)
    (hw₁a : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h)
    (hw₀a : ∃ h ∈ H, w₀ * a * w₀⁻¹ = a * h)
    (hw₀2 : w₀ * w₀ = 1)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) :
    a ∈ Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) := by
  obtain ⟨h₀, hh₀, e₀⟩ := hw₁a
  obtain ⟨h₁, hh₁, e₁⟩ := hw₀a
  have hw₂ : w₂ = w₁⁻¹ * w₀ := by rw [hw₀def]; group
  set X := w₁ * (a⁻¹ * w₂ * a) with hX
  have hXmem : X ∈ Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
      (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
  have hw₁a' : w₁ * a⁻¹ * w₁⁻¹ = h₀⁻¹ * a := by
    calc w₁ * a⁻¹ * w₁⁻¹ = (w₁ * a * w₁⁻¹)⁻¹ := by group
      _ = (a⁻¹ * h₀)⁻¹ := by rw [e₀]
      _ = h₀⁻¹ * a := by group
  have hw₀a' : w₀ * a = a * h₁ * w₀ := by
    calc w₀ * a = (w₀ * a * w₀⁻¹) * w₀ := by group
      _ = a * h₁ * w₀ := by rw [e₁]
  have hXe : X = h₀⁻¹ * a * a * h₁ * w₀ := by
    calc X = (w₁ * a⁻¹ * w₁⁻¹) * w₀ * a := by rw [hX, hw₂]; group
      _ = h₀⁻¹ * a * (w₀ * a) := by rw [hw₁a']; group
      _ = h₀⁻¹ * a * (a * h₁ * w₀) := by rw [hw₀a']
      _ = h₀⁻¹ * a * a * h₁ * w₀ := by group
  have hw₀P : w₀ * (h₀⁻¹ * a * a * h₁) * w₀⁻¹ = h₀ * a * h₁ * a := by
    have h1 : w₀ * h₀⁻¹ * w₀⁻¹ = h₀ := by rw [hinv _ (H.inv_mem hh₀), inv_inv]
    have h2 : w₀ * h₁ * w₀⁻¹ = h₁⁻¹ := hinv _ hh₁
    calc w₀ * (h₀⁻¹ * a * a * h₁) * w₀⁻¹
        = (w₀ * h₀⁻¹ * w₀⁻¹) * ((w₀ * a * w₀⁻¹) * (w₀ * a * w₀⁻¹)) * (w₀ * h₁ * w₀⁻¹) := by group
      _ = h₀ * ((a * h₁) * (a * h₁)) * h₁⁻¹ := by rw [h1, e₁, h2]
      _ = h₀ * a * h₁ * a := by group
  have hXX : X * X = h₀⁻¹ * (a * (a * (h₁ * h₀) * a⁻¹) * a⁻¹) * (a * a * a * h₁) * a := by
    calc X * X = (h₀⁻¹ * a * a * h₁ * w₀) * (h₀⁻¹ * a * a * h₁ * w₀) := by rw [hXe]
      _ = (h₀⁻¹ * a * a * h₁) * (w₀ * (h₀⁻¹ * a * a * h₁) * w₀⁻¹) * (w₀ * w₀) := by group
      _ = (h₀⁻¹ * a * a * h₁) * (h₀ * a * h₁ * a) * 1 := by rw [hw₀P, hw₀2]
      _ = h₀⁻¹ * (a * (a * (h₁ * h₀) * a⁻¹) * a⁻¹) * (a * a * a * h₁) * a := by group
  have hmH : h₀⁻¹ * (a * (a * (h₁ * h₀) * a⁻¹) * a⁻¹) * (a * a * a * h₁) ∈ H := by
    refine H.mul_mem (H.mul_mem (H.inv_mem hh₀) ?_) (H.mul_mem ha3 hh₁)
    exact haH _ (haH _ (H.mul_mem hh₁ hh₀))
  have hsub : (H : Set G) ⊆ (Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) : Set G) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hmN : h₀⁻¹ * (a * (a * (h₁ * h₀) * a⁻¹) * a⁻¹) * (a * a * a * h₁) ∈
      Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) := hsub hmH
  have : a = (h₀⁻¹ * (a * (a * (h₁ * h₀) * a⁻¹) * a⁻¹) * (a * a * a * h₁))⁻¹ * (X * X) := by
    rw [hXX]; group
  have hmem := Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) (Subgroup.mul_mem _ hXmem hXmem)
  rw [← this] at hmem
  exact hmem

end Algebra

end CFSG.GH74.GLS.Stage4.Rest
