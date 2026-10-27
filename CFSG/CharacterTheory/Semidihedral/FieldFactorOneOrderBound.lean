module

public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerOrderFormulas

public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem inv_gt_of_order_bound {g c d q X r : ℚ} (hg : 0 < g) (hc : 0 < c) (hd : 0 < d)
    (hq : 0 < q) (hX : 0 < X) (hr : q - 1 ≤ r)
    (hG : g = c ^ 3 / d ^ 2 * X * (r / q)) (hbound : 2 * q * g * d ^ 2 < 5 * c ^ 3 * (q - 1)) :
    (2 / 5 : ℚ) < 1 / X := by
  have hr0 : 0 < r := by
    have : 0 < 5 * c ^ 3 * (q - 1) := lt_of_le_of_lt (by positivity) hbound
    have hq1 : 0 < q - 1 := by
      by_contra h
      push Not at h
      nlinarith [pow_pos hc 3]
    linarith
  have key : 2 * X * (c ^ 3 * r) < 5 * c ^ 3 * r := by
    have e1 : 2 * q * g * d ^ 2 = 2 * X * (c ^ 3 * r) := by
      rw [hG]
      field_simp
    have e2 : 5 * c ^ 3 * (q - 1) ≤ 5 * c ^ 3 * r := by
      have : 0 ≤ 5 * c ^ 3 := by positivity
      nlinarith
    linarith
  have hcr : 0 < c ^ 3 * r := by positivity
  rw [lt_div_iff₀ hX]
  nlinarith

theorem principal_ratio_eq {f q e δ : ℚ} (hδ : δ = 1 ∨ δ = -1) :
    (δ * f - e * q) ^ 2 / (δ * f * (1 + δ * f)) = 1 / (f * (f + δ) / (f - e * δ * q) ^ 2) := by
  rcases hδ with rfl | rfl
  · rw [one_div_div]
    ring_nf
  · rw [one_div_div]
    ring_nf

theorem principal_quotients_gt_of_order_bound {G : Type} [Group G] [Finite G] {t s : G}
    {q : ℕ} {e δ₁ δ₂ : ℤ} {f₁ f₂ : ℕ} (hq : 1 < q) (he : e = 1 ∨ e = -1)
    (hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hf₁ : 1 < f₁) (hf₂ : 1 < f₂)
    (hOF : Principal.ActualPrincipalOrderFormulas G t s q e δ₁ δ₂ f₁ f₂)
    (hbound : 2 * q * Nat.card G * Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) ^ 2 <
      5 * Nat.card (C t) ^ 3 * (q - 1)) :
    (2 / 5 : ℚ) < ((δ₁ * f₁ : ℤ) - e * q * 1 : ℚ) ^ 2 /
        (1 * (δ₁ * f₁ : ℤ) * (1 + (δ₁ * f₁ : ℤ))) ∧
      (2 / 5 : ℚ) < ((δ₂ * f₂ : ℤ) + e * q * 1 : ℚ) ^ 2 /
        (1 * (δ₂ * f₂ : ℤ) * (1 + (δ₂ * f₂ : ℤ))) ∧
      ((δ₁ * f₁ : ℤ) - e * q * 1 : ℚ) ^ 2 / (1 * (δ₁ * f₁ : ℤ) * (1 + (δ₁ * f₁ : ℤ))) *
          ((q : ℚ) - e) =
        ((δ₂ * f₂ : ℤ) + e * q * 1 : ℚ) ^ 2 / (1 * (δ₂ * f₂ : ℤ) * (1 + (δ₂ * f₂ : ℤ))) *
          ((q : ℚ) + e) := by
  obtain ⟨hne₁, hne₂, hG₁, hG₂⟩ := hOF
  set g : ℚ := (Nat.card G : ℚ) with hg
  set c : ℚ := (Nat.card (C t) : ℚ) with hc
  set d : ℚ := (Nat.card ↥(C t ⊓ Subgroup.centralizer {s}) : ℚ) with hd
  have hg0 : 0 < g := by rw [hg]; exact_mod_cast Nat.card_pos
  have hc0 : 0 < c := by rw [hc]; exact_mod_cast Nat.card_pos
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Nat.card_pos
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hbound' : 2 * (q : ℚ) * g * d ^ 2 < 5 * c ^ 3 * ((q : ℚ) - 1) := by
    have h := (Nat.cast_lt (α := ℚ)).mpr hbound
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h
    exact h
  have heq : (e : ℚ) = 1 ∨ (e : ℚ) = -1 := by rcases he with rfl | rfl <;> norm_num
  have hδ₁q : (δ₁ : ℚ) = 1 ∨ (δ₁ : ℚ) = -1 := by rcases hδ₁ with rfl | rfl <;> norm_num
  have hδ₂q : (δ₂ : ℚ) = 1 ∨ (δ₂ : ℚ) = -1 := by rcases hδ₂ with rfl | rfl <;> norm_num
  have hf₁q : (1 : ℚ) < f₁ := by exact_mod_cast hf₁
  have hf₂q : (1 : ℚ) < f₂ := by exact_mod_cast hf₂
  set X₁ : ℚ := (f₁ : ℚ) * (f₁ + δ₁) / (f₁ - e * δ₁ * q) ^ 2 with hX₁def
  set X₂ : ℚ := (f₂ : ℚ) * (f₂ + δ₂) / (f₂ + e * δ₂ * q) ^ 2 with hX₂def
  have hX₁ : 0 < X₁ := by
    apply div_pos _ (by positivity)
    rcases hδ₁q with h | h <;> rw [h] <;> nlinarith
  have hX₂ : 0 < X₂ := by
    apply div_pos _ (by positivity)
    rcases hδ₂q with h | h <;> rw [h] <;> nlinarith
  have h₁ := inv_gt_of_order_bound hg0 hc0 hd0 hq0 hX₁
    (by rcases heq with h | h <;> linarith) hG₁ hbound'
  have h₂ := inv_gt_of_order_bound hg0 hc0 hd0 hq0 hX₂
    (by rcases heq with h | h <;> linarith) hG₂ hbound'
  have e1 : ((δ₁ * f₁ : ℤ) - e * q * 1 : ℚ) ^ 2 / (1 * (δ₁ * f₁ : ℤ) * (1 + (δ₁ * f₁ : ℤ))) =
      1 / X₁ := by
    push_cast
    rw [one_mul, mul_one]
    exact principal_ratio_eq hδ₁q
  have e2 : ((δ₂ * f₂ : ℤ) + e * q * 1 : ℚ) ^ 2 / (1 * (δ₂ * f₂ : ℤ) * (1 + (δ₂ * f₂ : ℤ))) =
      1 / X₂ := by
    push_cast
    rw [one_mul, mul_one, show (δ₂ : ℚ) * f₂ + e * q = δ₂ * f₂ - -e * q by ring,
      principal_ratio_eq (e := -e) hδ₂q, hX₂def,
      show (f₂ : ℚ) - -e * δ₂ * q = f₂ + e * δ₂ * q by ring]
  have hrel : X₁ * ((q : ℚ) + e) = X₂ * ((q : ℚ) - e) := by
    have h := hG₁.symm.trans hG₂
    have hk : c ^ 3 / d ^ 2 / q ≠ 0 := by positivity
    have h' : c ^ 3 / d ^ 2 / q * (X₁ * ((q : ℚ) + e)) =
        c ^ 3 / d ^ 2 / q * (X₂ * ((q : ℚ) - e)) := by
      calc c ^ 3 / d ^ 2 / q * (X₁ * ((q : ℚ) + e)) = c ^ 3 / d ^ 2 * X₁ * (((q : ℚ) + e) / q) := by
            ring
        _ = c ^ 3 / d ^ 2 * X₂ * (((q : ℚ) - e) / q) := h
        _ = c ^ 3 / d ^ 2 / q * (X₂ * ((q : ℚ) - e)) := by ring
    exact mul_left_cancel₀ hk h'
  refine ⟨e1 ▸ h₁, e2 ▸ h₂, ?_⟩
  rw [e1, e2]
  field_simp
  linarith [hrel]

end CFSG.Semidihedral.FieldFactorOne
