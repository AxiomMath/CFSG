module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseCharacters

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.Wreathed.ConditionalFourier

variable {m : ℕ} [NeZero m] {ζ : ℂ}

theorem zpow_eq_of_cast_eq (hζ : IsPrimitiveRoot ζ m) {a b : ℤ} (h : (a : ZMod m) = b) :
    ζ ^ a = ζ ^ b :=
  zpow_eq_of_modEq hζ ((ZMod.intCast_eq_intCast_iff_dvd_sub b a m).mp h.symm)

theorem intCast_val_cast (x : ZMod m) : (((x.val : ℤ)) : ZMod m) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

variable {A : Type*} [Group A] {σ υ : A}

theorem lam_zpow_mul_zpow (hζ : IsPrimitiveRoot ζ m) (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (i j : ZMod m) (a b : ℤ) :
    lam i j (σ ^ a * υ ^ b) = ζ ^ ((i.val : ℤ) * a + (j.val : ℤ) * b) :=
  linearCharacter_zpow_mul_zpow hζ (lam i j) (hlam i j).1 (hlam i j).2 a b

theorem inv_mul_pow_eq (hc : Commute σ υ) (k : ℕ) :
    ((σ * υ) ^ k)⁻¹ = σ ^ (-(k : ℤ)) * υ ^ (-(k : ℤ)) := by
  rw [hc.mul_pow, mul_inv_rev, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact ((hc.pow_pow k k).inv_inv).eq.symm

theorem conj_lam_mul_pow [Finite A] (hc : Commute σ υ) (hζ : IsPrimitiveRoot ζ m)
    (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (i j : ZMod m) (k : ℕ) :
    conj (lam i j ((σ * υ) ^ k)) = ζ ^ ((-i - j).val * k) := by
  rw [conj_monoidHom_apply, inv_mul_pow_eq hc, lam_zpow_mul_zpow hζ lam hlam, ← zpow_natCast]
  apply zpow_eq_of_cast_eq hζ
  push_cast
  simp only [ZMod.natCast_zmod_val]
  ring

omit [NeZero m] in
theorem conj_lam_inv_left [Finite A] (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (i j : ZMod m) (k : ℕ) :
    conj (lam i j (σ ^ k)⁻¹) = ζ ^ (i.val * k) := by
  rw [conj_monoidHom_apply, inv_inv, map_pow, (hlam i j).1, ← pow_mul]

omit [NeZero m] in
theorem conj_lam_inv_right [Finite A] (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (i j : ZMod m) (k : ℕ) :
    conj (lam i j (υ ^ k)⁻¹) = ζ ^ (j.val * k) := by
  rw [conj_monoidHom_apply, inv_inv, map_pow, (hlam i j).2, ← pow_mul]

omit [NeZero m] in
theorem lam_zero (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
    (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (x : A) : lam 0 0 x = 1 := by
  have h := monoidHom_ext_pair hc hgen (lam 0 0) 1 (by rw [(hlam 0 0).1]; simp)
    (by rw [(hlam 0 0).2]; simp)
  rw [h, MonoidHom.one_apply]

variable [Fintype A] (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
  (hσ : orderOf σ = m) (hυ : orderOf υ = m)
  (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
  (lam : ZMod m → ZMod m → A →* ℂ)
  (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val)

include hc hgen hσ hυ hint hζ hlam in
theorem card_mul_column_eq (P : Finset A)
    (hsplit : ∀ F : A → ℂ, ∑ x, F x = F 1 + ∑ k ∈ Finset.Ico 1 m,
      (F ((σ * υ) ^ k) + F (σ ^ k)⁻¹ + F (υ ^ k)⁻¹) + ∑ x ∈ P, F x)
    (χ : A → ℂ) (v : ℕ → Fin 2 → ℂ) (q₀ : ℂ)
    (hconj : ∀ k ∈ Finset.Ico 1 m,
      χ (σ ^ k)⁻¹ = χ ((σ * υ) ^ k) ∧ χ (υ ^ k)⁻¹ = χ ((σ * υ) ^ k))
    (hval : ∀ k ∈ Finset.Ico 1 m, χ ((σ * υ) ^ k) = v k 0 + (2 + m * q₀) * v k 1)
    (i j : ZMod m) :
    (Fintype.card A : ℂ) *
        (((Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * conj (lam 0 0 x)) -
          ((Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * conj (lam i j x)) +
          q₀ * (fourierTransform m ζ (fun k => v k 1) i.val +
            fourierTransform m ζ (fun k => v k 1) j.val +
            fourierTransform m ζ (fun k => v k 1) (-i - j).val)) =
      ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) +
          (1 - conj (lam i j (σ ^ k)⁻¹)) + (1 - conj (lam i j (υ ^ k)⁻¹))) *
          (v k 0 + 2 * v k 1) +
        ∑ x ∈ P, (1 - conj (lam i j x)) * χ x := by
  have hcard : (Fintype.card A : ℂ) = (m : ℂ) ^ 2 := by
    rw [card_eq_sq hc hgen hσ hυ hint hζ lam hlam]
    push_cast
    ring
  have hA0 : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have ht : (Fintype.card A : ℂ) * (((Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * conj (lam 0 0 x)) -
      ((Fintype.card A : ℂ)⁻¹ * ∑ x, χ x * conj (lam i j x))) =
      ∑ x, (1 - conj (lam i j x)) * χ x := by
    rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hA0, one_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lam_zero hc hgen lam hlam, map_one]
    ring
  have hF : ∀ x : ZMod m, fourierTransform m ζ (fun k => v k 1) x.val =
      (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (x.val * k) - 1) * v k 1 := fun x => rfl
  have hBk : ∀ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) +
      (1 - conj (lam i j (σ ^ k)⁻¹)) + (1 - conj (lam i j (υ ^ k)⁻¹))) =
      -((ζ ^ (i.val * k) - 1) + (ζ ^ (j.val * k) - 1) + (ζ ^ ((-i - j).val * k) - 1)) := by
    intro k _
    rw [conj_lam_mul_pow hc hζ lam hlam, conj_lam_inv_left lam hlam,
      conj_lam_inv_right lam hlam]
    ring
  rw [mul_add, ht, hsplit (fun x => (1 - conj (lam i j x)) * χ x), hF, hF, hF]
  simp only [map_one, sub_self, zero_mul, zero_add]
  have hcentral : ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) * χ ((σ * υ) ^ k) +
      (1 - conj (lam i j (σ ^ k)⁻¹)) * χ (σ ^ k)⁻¹ +
      (1 - conj (lam i j (υ ^ k)⁻¹)) * χ (υ ^ k)⁻¹) =
      ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) +
        (1 - conj (lam i j (σ ^ k)⁻¹)) + (1 - conj (lam i j (υ ^ k)⁻¹))) *
          (v k 0 + 2 * v k 1) +
      (m : ℂ) * q₀ * ∑ k ∈ Finset.Ico 1 m, -((ζ ^ (i.val * k) - 1) + (ζ ^ (j.val * k) - 1) +
        (ζ ^ ((-i - j).val * k) - 1)) * v k 1 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(hconj k hk).1, (hconj k hk).2, hval k hk, ← hBk k hk]
    ring
  rw [hcentral, hcard]
  have hsum : ∀ (f : ℕ → ℂ), ∑ k ∈ Finset.Ico 1 m, -((ζ ^ (i.val * k) - 1) +
      (ζ ^ (j.val * k) - 1) + (ζ ^ ((-i - j).val * k) - 1)) * f k =
      -(∑ k ∈ Finset.Ico 1 m, (ζ ^ (i.val * k) - 1) * f k +
        ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j.val * k) - 1) * f k +
        ∑ k ∈ Finset.Ico 1 m, (ζ ^ ((-i - j).val * k) - 1) * f k) := by
    intro f
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  field_simp
  ring

end CFSG.Wreathed.ConditionalGeneralBase
