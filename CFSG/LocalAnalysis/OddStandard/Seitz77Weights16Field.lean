module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Bi

public section

namespace CFSG.OddStandard.Seitz77

namespace Weights16

open CFSG.GH74.KGroups

theorem bilin_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (c : Fin 4 → Fin 4 → R) (x y : R) :
    φ (bilin c x y) = bilin (fun i j => φ (c i j)) (φ x) (φ y) := by
  simp only [bilin]
  rw [lin_map]
  congr 1
  funext j
  exact lin_map φ _ x

variable {F : Type*} [Field F]

theorem exists_ringEquiv (hF : Nat.card F = 16) : Nonempty (GF16 ≃+* F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype F := Fintype.ofFinite F
  have h1 : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h2 : Fintype.card GF16 = 16 := by decide
  exact ⟨FiniteField.ringEquivOfCardEq (h2.trans h1.symm)⟩

theorem nat_card_galoisField : Nat.card (GaloisField 2 4) = 16 := by
  have := GaloisField.card 2 4 (by norm_num)
  simpa using this

theorem inv_eq_pow_fourteen {z : F} (hz : orderOf z = 15) : z⁻¹ = z ^ 14 := by
  have h : z * z ^ 14 = 1 := by
    rw [← pow_succ', show 14 + 1 = orderOf z by rw [hz]]
    exact pow_orderOf_eq_one z
  exact inv_eq_of_mul_eq_one_right h

theorem orderOf_eq_fifteen_of_pow_four (hF : Nat.card F = 16) {z : F} (hz : z ^ 4 = z + 1) :
    orderOf z = 15 := by
  obtain ⟨φ⟩ := exists_ringEquiv hF
  have h1 : φ.symm z ^ 4 = φ.symm z + 1 := by rw [← map_pow, hz, map_add, map_one]
  have h2 : ∀ r : GF16, r ^ 4 = r + 1 → r ^ 15 = 1 ∧ ∀ m < 15, 0 < m → r ^ m ≠ 1 := by
    decide +kernel
  have h3 : orderOf (φ.symm z) = 15 := (orderOf_eq_iff (by norm_num)).2 (h2 _ h1)
  have := φ.toMulEquiv.orderOf_eq (φ.symm z)
  simpa [h3] using this

theorem exists_pow_four_eq (hF : Nat.card F = 16) : ∃ z : F, z ^ 4 = z + 1 := by
  obtain ⟨φ⟩ := exists_ringEquiv hF
  exact ⟨φ zeta, by rw [← map_pow, zeta_pow_four, map_add, map_one]⟩

theorem additive_weight_field (hF : Nat.card F = 16) {z : F} (hz : orderOf z = 15) (a b : ℕ)
    {f : F → F} (hf : ∀ x y, f (x + y) = f x + f y) (hzf : ∀ x, f (z ^ a * x) = z ^ b * f x) :
    ∃ c : Fin 4 → F, (∀ x, f x = lin c x) ∧
      ∀ i : Fin 4, c i ≠ 0 → a * 2 ^ (i : ℕ) ≡ b [MOD 15] := by
  obtain ⟨φ⟩ := exists_ringEquiv hF
  have hr : orderOf (φ.symm z) = 15 := by
    have := φ.symm.toMulEquiv.orderOf_eq z
    simpa [hz] using this
  obtain ⟨c, hc, hc'⟩ := additive_weight hr a b (f := fun x => φ.symm (f (φ x)))
    (fun x y => by simp only [map_add, hf])
    (fun x => by simp only [map_mul, map_pow, RingEquiv.apply_symm_apply, hzf])
  refine ⟨fun i => φ (c i), fun x => ?_, fun i hi => hc' i fun h0 => hi (by simp [h0])⟩
  have h1 : f x = φ (lin c (φ.symm x)) := by
    rw [← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have h2 := lin_map (φ : GF16 →+* F) c (φ.symm x)
  simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply] at h2
  rw [h1, h2]

theorem biadditive_weight_field (hF : Nat.card F = 16) {z : F} (hz : orderOf z = 15)
    (a b e : ℕ) {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (hzβ : ∀ x y, β (z ^ a * x) (z ^ b * y) = z ^ e * β x y) :
    ∃ c : Fin 4 → Fin 4 → F, (∀ x y, β x y = bilin c x y) ∧
      ∀ i j : Fin 4, c i j ≠ 0 → a * 2 ^ (i : ℕ) + b * 2 ^ (j : ℕ) ≡ e [MOD 15] := by
  obtain ⟨φ⟩ := exists_ringEquiv hF
  have hr : orderOf (φ.symm z) = 15 := by
    have := φ.symm.toMulEquiv.orderOf_eq z
    simpa [hz] using this
  obtain ⟨c, hc, hc'⟩ := biadditive_weight hr a b e (β := fun x y => φ.symm (β (φ x) (φ y)))
    (fun x x' y => by simp only [map_add, hx])
    (fun x y y' => by simp only [map_add, hy])
    (fun x y => by simp only [map_mul, map_pow, RingEquiv.apply_symm_apply, hzβ])
  refine ⟨fun i j => φ (c i j), fun x y => ?_,
    fun i j hij => hc' i j fun h0 => hij (by simp [h0])⟩
  have h1 : β x y = φ (bilin c (φ.symm x) (φ.symm y)) := by
    rw [← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have h2 := bilin_map (φ : GF16 →+* F) c (φ.symm x) (φ.symm y)
  simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply] at h2
  rw [h1, h2]

end Weights16

end CFSG.OddStandard.Seitz77
