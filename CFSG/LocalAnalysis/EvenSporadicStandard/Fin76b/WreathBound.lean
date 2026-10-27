module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {Y : Type*} [Group Y]

theorem eq_of_mul_eq_mul {N₁ N₂ : Subgroup Y} (hd : Disjoint N₁ N₂) {a a' b b' : Y}
    (ha : a ∈ N₁) (ha' : a' ∈ N₁) (hb : b ∈ N₂) (hb' : b' ∈ N₂) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hm1 : a'⁻¹ * a ∈ N₁ := N₁.mul_mem (N₁.inv_mem ha') ha
  have hm2 : a'⁻¹ * a ∈ N₂ := by rw [h1]; exact N₂.mul_mem hb' (N₂.inv_mem hb)
  have h0 : a'⁻¹ * a = 1 := Subgroup.disjoint_def.1 hd hm1 hm2
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h0, mul_one]
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

theorem wreath_sq_eq_one {N₁ N₂ : Subgroup Y} {σ : Y}
    (hc : N₂ ≤ centralizer (N₁ : Set Y)) (hd : Disjoint N₁ N₂)
    (hσ2 : σ * σ = 1) (hσ : N₁.map (MulAut.conj σ).toMonoidHom = N₂)
    (hF₁ : ∀ P : Subgroup Y, P ≤ N₁ → Nat.card P = 8 → ∀ a ∈ N₁,
      (∀ x ∈ P, a * x = x * a) → a * a = 1)
    (hF₂ : ∀ P : Subgroup Y, P ≤ N₂ → Nat.card P = 8 → ∀ a ∈ N₂,
      (∀ x ∈ P, a * x = x * a) → a * a = 1)
    (D : Subgroup Y) (hD8 : Nat.card D = 8) (hDN : D ≤ N₁ ⊔ N₂)
    (hDσ : ∀ d ∈ D, σ * d * σ⁻¹ = d) {u : Y} (hu : u ∈ N₁ ⊔ N₂)
    (huD : ∀ d ∈ D, u * d = d * u) : u * u = 1 := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσ2' : ∀ x ∈ N₁, σ * x * σ⁻¹ ∈ N₂ := by
    intro x hx
    rw [← hσ]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hσ1 : ∀ y ∈ N₂, σ * y * σ⁻¹ ∈ N₁ := by
    intro y hy
    rw [← hσ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have : σ * ((MulAut.conj σ).toMonoidHom x) * σ⁻¹ = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hσinv]
      calc σ * (σ * x * σ) * σ = (σ * σ) * x * (σ * σ) := by group
        _ = x := by rw [hσ2]; simp
    rw [this]
    exact hx
  have hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 (hc hy) x hx
  have hdiag : ∀ d ∈ D, ∃ x ∈ N₁, d = x * (σ * x * σ⁻¹) := by
    intro d hd'
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup_of_le_centralizer hc (hDN hd')
    refine ⟨x, hx, ?_⟩
    have h1 : σ * d * σ⁻¹ = d := hDσ d hd'
    have h2 : σ * d * σ⁻¹ = (σ * y * σ⁻¹) * (σ * x * σ⁻¹) := by
      rw [hxy]
      calc σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
        _ = (σ * y * σ⁻¹) * (σ * x * σ⁻¹) := (hcomm _ (hσ1 y hy) _ (hσ2' x hx)).symm
    have h3 : (σ * y * σ⁻¹) * (σ * x * σ⁻¹) = x * y := by rw [← h2, h1, hxy]
    obtain ⟨hxx, hyy⟩ := eq_of_mul_eq_mul hd (hσ1 y hy) hx (hσ2' x hx) hy h3
    rw [hxy, ← hyy]
  let P : Subgroup Y :=
    { carrier := {x | x ∈ N₁ ∧ x * (σ * x * σ⁻¹) ∈ D}
      mul_mem' := by
        rintro x x' ⟨hx, hxD⟩ ⟨hx', hx'D⟩
        refine ⟨N₁.mul_mem hx hx', ?_⟩
        have : x * x' * (σ * (x * x') * σ⁻¹) =
            (x * (σ * x * σ⁻¹)) * (x' * (σ * x' * σ⁻¹)) := by
          calc x * x' * (σ * (x * x') * σ⁻¹)
              = x * x' * ((σ * x * σ⁻¹) * (σ * x' * σ⁻¹)) := by group
            _ = x * (x' * (σ * x * σ⁻¹)) * (σ * x' * σ⁻¹) := by group
            _ = x * ((σ * x * σ⁻¹) * x') * (σ * x' * σ⁻¹) := by
                rw [hcomm x' hx' _ (hσ2' x hx)]
            _ = (x * (σ * x * σ⁻¹)) * (x' * (σ * x' * σ⁻¹)) := by group
        rw [this]
        exact D.mul_mem hxD hx'D
      one_mem' := ⟨N₁.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxD⟩
        refine ⟨N₁.inv_mem hx, ?_⟩
        have hy : σ * x * σ⁻¹ ∈ N₂ := hσ2' x hx
        have h1 : x⁻¹ * (σ * x⁻¹ * σ⁻¹) = (x * (σ * x * σ⁻¹))⁻¹ := by
          have hc' := hcomm x⁻¹ (N₁.inv_mem hx) _ (N₂.inv_mem hy)
          calc x⁻¹ * (σ * x⁻¹ * σ⁻¹) = x⁻¹ * (σ * x * σ⁻¹)⁻¹ := by group
            _ = (σ * x * σ⁻¹)⁻¹ * x⁻¹ := hc'
            _ = (x * (σ * x * σ⁻¹))⁻¹ := by group
        rw [h1]
        exact D.inv_mem hxD }
  have hPle : P ≤ N₁ := fun x hx => hx.1
  have hPcard : Nat.card P = 8 := by
    rw [← hD8]
    refine Nat.card_eq_of_bijective (fun x : P => (⟨x.1 * (σ * x.1 * σ⁻¹), x.2.2⟩ : D))
      ⟨?_, ?_⟩
    · intro x x' hxx'
      have h1 := congrArg Subtype.val hxx'
      simp only at h1
      exact Subtype.ext (eq_of_mul_eq_mul hd x.2.1 x'.2.1 (hσ2' _ x.2.1) (hσ2' _ x'.2.1) h1).1
    · intro d
      obtain ⟨x, hx, hdx⟩ := hdiag d d.2
      refine ⟨⟨x, hx, by rw [← hdx]; exact d.2⟩, Subtype.ext hdx.symm⟩
  have hP2 := P.map (MulAut.conj σ).toMonoidHom
  have hP2le : P.map (MulAut.conj σ).toMonoidHom ≤ N₂ := by
    rw [← hσ]
    exact Subgroup.map_mono hPle
  have hP2card : Nat.card (P.map (MulAut.conj σ).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]
    exact hPcard
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hc hu
  have hcomm_ab : ∀ x ∈ P, a * x = x * a ∧ b * (σ * x * σ⁻¹) = (σ * x * σ⁻¹) * b := by
    intro x hx
    have hy := hσ2' x hx.1
    have h1 := huD _ hx.2
    rw [hab] at h1
    have h2 : (a * x) * (b * (σ * x * σ⁻¹)) = (x * a) * ((σ * x * σ⁻¹) * b) := by
      calc (a * x) * (b * (σ * x * σ⁻¹)) = a * (x * b) * (σ * x * σ⁻¹) := by group
        _ = a * (b * x) * (σ * x * σ⁻¹) := by rw [hcomm x hx.1 b hb]
        _ = a * b * (x * (σ * x * σ⁻¹)) := by group
        _ = x * (σ * x * σ⁻¹) * (a * b) := h1
        _ = x * ((σ * x * σ⁻¹) * a) * b := by group
        _ = x * (a * (σ * x * σ⁻¹)) * b := by rw [hcomm a ha _ hy]
        _ = (x * a) * ((σ * x * σ⁻¹) * b) := by group
    exact eq_of_mul_eq_mul hd (N₁.mul_mem ha hx.1) (N₁.mul_mem hx.1 ha)
      (N₂.mul_mem hb hy) (N₂.mul_mem hy hb) h2
  have haa : a * a = 1 := hF₁ P hPle hPcard a ha fun x hx => (hcomm_ab x hx).1
  have hbb : b * b = 1 := by
    refine hF₂ _ hP2le hP2card b hb ?_
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using (hcomm_ab x hx).2
  rw [hab]
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hcomm a ha b hb]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [haa, hbb, one_mul]

end CFSG.EvenSporadicStandard.Fin76b
