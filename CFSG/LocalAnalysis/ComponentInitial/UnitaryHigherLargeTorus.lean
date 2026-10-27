module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {K : Type} [Field K]

theorem closure_eq_top (h : UnitaryFieldData p f K) {H : Subgroup Kˣ}
    (hH : p ^ f - 1 < Nat.card H) :
    Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤ := by
  have := h.finite
  set F₀ := Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) with hF₀
  have : Finite F₀ := Subtype.finite
  have hHF : Nat.card H ≤ Nat.card F₀ - 1 := by
    rw [← Nat.card_units]
    refine Nat.card_le_card_of_injective (fun u => Units.mk0 ⟨(u : Kˣ), Subfield.subset_closure
      ⟨u, u.2, rfl⟩⟩ fun h0 => (u : Kˣ).ne_zero (congrArg Subtype.val h0)) fun u v huv => ?_
    have := congrArg (fun x : F₀ˣ => ((x : F₀) : K)) huv
    exact Subtype.ext (Units.ext this)
  have hcard := Module.natCard_eq_pow_finrank (K := F₀) (V := K)
  rw [UnitaryFieldData.card_eq_sq h] at hcard
  have hq : 2 ≤ p ^ f := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  by_contra hne
  have hpos : 0 < Nat.card F₀ := Nat.card_pos
  have hd : 2 ≤ finrank F₀ K := by
    by_contra hd
    have hd1 : finrank F₀ K = 1 ∨ finrank F₀ K = 0 := by omega
    rcases hd1 with hd1 | hd1
    · apply hne
      rw [hd1, pow_one] at hcard
      refine eq_top_iff.mpr fun x _ => ?_
      have hbij := (Nat.bijective_iff_injective_and_card (fun y : F₀ => (y : K))).mpr
        ⟨Subtype.val_injective, by rw [UnitaryFieldData.card_eq_sq h, hcard]⟩
      obtain ⟨y, rfl⟩ := hbij.2 x
      exact y.2
    · rw [hd1, pow_zero] at hcard
      have h1 : 1 < (p ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
  have h2 : Nat.card F₀ ^ 2 ≤ (p ^ f) ^ 2 := by
    rw [hcard]
    exact Nat.pow_le_pow_right hpos hd
  have h3 : Nat.card F₀ ≤ p ^ f := (Nat.pow_le_pow_iff_left two_ne_zero).mp h2
  omega

theorem map_mul_eq_of_mem_closure {H : Subgroup Kˣ} (A : K ≃+ K)
    (hA : ∀ u ∈ H, ∃ u' ∈ H, ∀ y : K, A ((u : K) * y) = u' * A y) {x : K}
    (hx : x ∈ Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ))) :
    ∀ y : K, A (x * y) = A x * (A 1)⁻¹ * A y := by
  have hA1 : A 1 ≠ 0 := fun h0 => one_ne_zero (A.injective (h0.trans (map_zero A).symm))
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', -, hu'⟩ := hA u hu
    intro y
    have h1 := hu' 1
    rw [mul_one] at h1
    rw [hu', h1]
    field_simp
  | one =>
    intro y
    rw [one_mul, mul_inv_cancel₀ hA1, one_mul]
  | add x x' _ _ hx hx' =>
    intro y
    rw [add_mul, map_add, map_add, hx, hx', add_mul, add_mul]
  | neg x _ hx =>
    intro y
    rw [neg_mul, map_neg, map_neg, hx, neg_mul, neg_mul]
  | inv x _ hx =>
    intro y
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero, zero_mul, map_zero, zero_mul, zero_mul]
    have hAx : A x ≠ 0 := fun h0 => hx0 (A.injective (h0.trans (map_zero A).symm))
    have h1 := hx (x⁻¹ * y)
    rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    have h2 := hx x⁻¹
    rw [mul_inv_cancel₀ hx0] at h2
    generalize A (x⁻¹ * y) = w at h1 ⊢
    generalize A x⁻¹ = v at h2 ⊢
    generalize A y = z at h1 ⊢
    generalize A x = a at h1 h2 hAx
    generalize A 1 = c at h1 h2 hA1 ⊢
    have hv : v = c * c * a⁻¹ := by
      field_simp at h2 ⊢
      linear_combination -h2
    rw [h1, hv]
    field_simp
  | mul x x' _ _ hx hx' =>
    intro y
    rw [show x * x' * y = x * (x' * y) from mul_assoc x x' y, hx, hx' y, hx x']
    ring

theorem unitary_large_torus_additive_normalizer (h : UnitaryFieldData p f K) {H : Subgroup Kˣ}
    (hH : p ^ f - 1 < Nat.card H) (A : K ≃+ K)
    (hA : (A.toEquiv : Equiv.Perm K) ∈ Subgroup.normalizer
      ((H.map (MulAction.toPermHom Kˣ K) : Subgroup (Equiv.Perm K)) : Set (Equiv.Perm K))) :
    ∃ (c : Kˣ) (σ : K ≃+* K), ∀ x : K, A x = c * σ x := by
  have := h.finite
  have hA1 : A 1 ≠ 0 := fun h0 => one_ne_zero (A.injective (h0.trans (map_zero A).symm))
  have hA' : ∀ u ∈ H, ∃ u' ∈ H, ∀ y : K, A ((u : K) * y) = u' * A y := by
    intro u hu
    have h1 := (Subgroup.mem_normalizer_iff.mp hA (MulAction.toPermHom Kˣ K u)).mp ⟨u, hu, rfl⟩
    obtain ⟨u', hu', he⟩ := h1
    refine ⟨u', hu', fun y => ?_⟩
    have h2 := congrArg (fun g : Equiv.Perm K => g (A y)) he
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv] at h2
    have h3 : A.toEquiv.symm (A y) = y := A.toEquiv.symm_apply_apply y
    rw [h3] at h2
    exact h2.symm
  have hall : ∀ x y : K, A (x * y) = A x * (A 1)⁻¹ * A y := fun x =>
    map_mul_eq_of_mem_closure A hA' (by rw [closure_eq_top h hH]; exact Subfield.mem_top x)
  let σ₀ : K →+* K :=
    { toFun := fun x => A x * (A 1)⁻¹
      map_one' := mul_inv_cancel₀ hA1
      map_mul' := fun x y => by
        rw [hall x y]
        ring
      map_zero' := by rw [map_zero, zero_mul]
      map_add' := fun x y => by rw [map_add, add_mul] }
  have hσinj : Function.Injective σ₀ := σ₀.injective
  have hσ : Function.Bijective σ₀ := ⟨hσinj, Finite.surjective_of_injective hσinj⟩
  refine ⟨Units.mk0 (A 1) hA1, RingEquiv.ofBijective σ₀ hσ, fun x => ?_⟩
  change A x = A 1 * (A x * (A 1)⁻¹)
  rw [mul_comm (A x), ← mul_assoc, mul_inv_cancel₀ hA1, one_mul]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
