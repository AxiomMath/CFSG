module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GH74.GLS.SP.Local

private theorem exists_halving {H : Type} [CommGroup H] (hodd : Odd (Nat.card H)) :
    ∃ r : H →* H, (∀ x, r (x * x) = x) ∧ ∀ (σ : H →* H) x, σ (r x) = r (σ x) := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨powMonoidHom (k + 1), fun x => ?_, fun σ x => map_pow σ x (k + 1)⟩
  calc powMonoidHom (k + 1) (x * x) = x ^ (2 * (k + 1)) := by
        rw [powMonoidHom_apply, ← sq, ← pow_mul]
    _ = x ^ Nat.card H * x := by rw [← pow_succ]; congr 1; omega
    _ = x := by rw [pow_card_eq_one', one_mul]

private theorem split_one {H : Type} [CommGroup H] (r : H →* H) (hr : ∀ x, r (x * x) = x)
    (hrσ : ∀ (σ : H →* H) x, σ (r x) = r (σ x)) (σ : H →* H) (hσ : ∀ x, σ (σ x) = x) (x : H) :
    σ (r (x * σ x)) = r (x * σ x) ∧ σ (r (x * (σ x)⁻¹)) = (r (x * (σ x)⁻¹))⁻¹ ∧
      r (x * σ x) * r (x * (σ x)⁻¹) = x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hrσ σ, map_mul σ, hσ, mul_comm (σ x) x]
  · rw [hrσ σ, map_mul σ, map_inv σ, hσ, ← map_inv r, mul_inv_rev, inv_inv]
  · rw [← map_mul r, mul_mul_mul_comm, mul_inv_cancel, mul_one, hr]

private theorem inv_part_inv {H : Type} [CommGroup H] (r : H →* H)
    (hrσ : ∀ (σ : H →* H) x, σ (r x) = r (σ x)) (σ τ : H →* H) (hστ : ∀ y, τ (σ y) = σ (τ y))
    (x : H) (hx : τ x = x⁻¹) : τ (r (x * (σ x)⁻¹)) = (r (x * (σ x)⁻¹))⁻¹ := by
  rw [hrσ τ, map_mul τ, map_inv τ, hστ, hx, map_inv σ, ← map_inv r, mul_inv_rev, inv_inv,
    mul_comm x⁻¹ (σ x)]

private theorem split_of_involutions {H : Type} [Group H] (hc : ∀ x y : H, x * y = y * x)
    (hodd : Odd (Nat.card H)) (σ₁ σ₂ : H →* H) (h1 : ∀ x, σ₁ (σ₁ x) = x)
    (h2 : ∀ x, σ₂ (σ₂ x) = x) (h12 : ∀ x, σ₁ (σ₂ x) = σ₂ (σ₁ x)) (a : H) :
    ∃ a₁ a₂ a₃ : H, σ₁ a₁ = a₁ ∧ σ₂ a₂ = a₂ ∧ σ₁ (σ₂ a₃) = a₃ ∧ a = a₁ * a₂ * a₃ := by
  let _ : CommGroup H := CommGroup.mk hc
  obtain ⟨r, hr, hrσ⟩ := exists_halving (H := H) hodd
  obtain ⟨a₁, b, hf₁, hb, hab⟩ : ∃ a₁ b, σ₁ a₁ = a₁ ∧ σ₁ b = b⁻¹ ∧ a = a₁ * b := by
    obtain ⟨hf, hi, hs⟩ := split_one r hr hrσ σ₁ h1 a
    exact ⟨_, _, hf, hi, hs.symm⟩
  obtain ⟨a₂, a₃, hf₂, hf₃, hb'⟩ : ∃ a₂ a₃, σ₂ a₂ = a₂ ∧ σ₁ (σ₂ a₃) = a₃ ∧ b = a₂ * a₃ := by
    obtain ⟨hf, hi, hs⟩ := split_one r hr hrσ σ₂ h2 b
    refine ⟨_, _, hf, ?_, hs.symm⟩
    rw [hi, map_inv σ₁, inv_part_inv r hrσ σ₂ σ₁ h12 b hb, inv_inv]
  exact ⟨a₁, a₂, a₃, hf₁, hf₂, hf₃, by rw [hab, hb', mul_assoc]⟩

private def conjHom {G : Type} [Group G] (A : Subgroup G) (u : G)
    (hu : ∀ a ∈ A, u * a * u⁻¹ ∈ A) : A →* A where
  toFun a := ⟨u * a * u⁻¹, hu a a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left])

private theorem conjHom_coe {G : Type} [Group G] (A : Subgroup G) (u : G)
    (hu : ∀ a ∈ A, u * a * u⁻¹ ∈ A) (a : A) : (conjHom A u hu a : G) = u * a * u⁻¹ := rfl

private theorem conj_conj {G : Type} [Group G] (u v x : G) :
    u * (v * x * v⁻¹) * u⁻¹ = (u * v) * x * (u * v)⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

open Subgroup in
theorem four_group_generation {G : Type} [Group G] (A : Subgroup G)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAodd : Odd (Nat.card ↥A))
    (u₁ u₂ : G) (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁)
    (hn₁ : ∀ a ∈ A, u₁ * a * u₁⁻¹ ∈ A) (hn₂ : ∀ a ∈ A, u₂ * a * u₂⁻¹ ∈ A) :
    ∀ a ∈ A, ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A,
      u₁ * a₁ * u₁⁻¹ = a₁ ∧ u₂ * a₂ * u₂⁻¹ = a₂ ∧ (u₁ * u₂) * a₃ * (u₁ * u₂)⁻¹ = a₃ ∧
        a = a₁ * a₂ * a₃ := by
  intro a ha
  have i₁ : u₁⁻¹ = u₁ := inv_eq_of_mul_eq_one_right h1
  have i₂ : u₂⁻¹ = u₂ := inv_eq_of_mul_eq_one_right h2
  have inv₁ : ∀ x : A, conjHom A u₁ hn₁ (conjHom A u₁ hn₁ x) = x := by
    intro x
    apply Subtype.ext
    rw [conjHom_coe, conjHom_coe, i₁]
    calc u₁ * (u₁ * (x : G) * u₁) * u₁ = (u₁ * u₁) * x * (u₁ * u₁) := by simp only [mul_assoc]
      _ = x := by rw [h1, one_mul, mul_one]
  have inv₂ : ∀ x : A, conjHom A u₂ hn₂ (conjHom A u₂ hn₂ x) = x := by
    intro x
    apply Subtype.ext
    rw [conjHom_coe, conjHom_coe, i₂]
    calc u₂ * (u₂ * (x : G) * u₂) * u₂ = (u₂ * u₂) * x * (u₂ * u₂) := by simp only [mul_assoc]
      _ = x := by rw [h2, one_mul, mul_one]
  have comm₁₂ : ∀ x : A,
      conjHom A u₁ hn₁ (conjHom A u₂ hn₂ x) = conjHom A u₂ hn₂ (conjHom A u₁ hn₁ x) := by
    intro x
    apply Subtype.ext
    rw [conjHom_coe, conjHom_coe, conjHom_coe, conjHom_coe]
    calc u₁ * (u₂ * (x : G) * u₂⁻¹) * u₁⁻¹ = (u₁ * u₂) * x * (u₁ * u₂)⁻¹ := conj_conj u₁ u₂ x
      _ = (u₂ * u₁) * x * (u₂ * u₁)⁻¹ := by rw [h12]
      _ = u₂ * (u₁ * (x : G) * u₁⁻¹) * u₂⁻¹ := (conj_conj u₂ u₁ x).symm
  obtain ⟨b₁, b₂, b₃, e₁, e₂, e₃, e⟩ := split_of_involutions
    (fun x y => Subtype.ext (hAc x x.2 y y.2)) hAodd (conjHom A u₁ hn₁) (conjHom A u₂ hn₂)
    inv₁ inv₂ comm₁₂ ⟨a, ha⟩
  refine ⟨b₁, b₁.2, b₂, b₂.2, b₃, b₃.2, congrArg Subtype.val e₁, congrArg Subtype.val e₂, ?_,
    congrArg Subtype.val e⟩
  have e₃' := congrArg Subtype.val e₃
  rw [conjHom_coe, conjHom_coe] at e₃'
  calc (u₁ * u₂) * (b₃ : G) * (u₁ * u₂)⁻¹ = u₁ * (u₂ * (b₃ : G) * u₂⁻¹) * u₁⁻¹ :=
        (conj_conj u₁ u₂ b₃).symm
    _ = b₃ := e₃'

end CFSG.GH74.GLS.SP.Local
