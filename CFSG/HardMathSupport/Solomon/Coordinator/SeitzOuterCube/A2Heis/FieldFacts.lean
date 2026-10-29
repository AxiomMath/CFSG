module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Arith

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis

open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF)

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem finrank_fixF (hσ : orderOf σ = 3) : Module.finrank (fixF σ) F = 3 := by
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) DFunLike.coe_injective
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have h1 := FixedPoints.finrank_eq_card (Subgroup.zpowers σ) F
  rw [← hσ, ← Nat.card_zpowers, Nat.card_eq_fintype_card]
  exact h1

theorem card_eq_cube (hσ : orderOf σ = 3) : Nat.card F = Nat.card (fixF σ) ^ 3 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (fixF σ) := Fintype.ofFinite _
  have h2 := Module.card_eq_pow_finrank (K := fixF σ) (V := F)
  rw [finrank_fixF hσ] at h2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h2

theorem pow_card_sub_one_of_fixed {y : F} (hy0 : y ≠ 0) (hy : σ y = y) :
    y ^ (Nat.card (fixF σ) - 1) = 1 := by
  have : Fintype (fixF σ) := Fintype.ofFinite _
  have hy' : (⟨y, mem_fixF.2 hy⟩ : fixF σ) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one (⟨y, mem_fixF.2 hy⟩ : fixF σ) hy'
  rw [Nat.card_eq_fintype_card]
  exact congrArg Subtype.val this

theorem two_le_card_fixF : 2 ≤ Nat.card (fixF σ) := by
  have : Fintype (fixF σ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

theorem cube_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h : q ^ 3 = (q - 1) * (q ^ 2 + q + 1) + 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.sub_eq_of_eq_add h

theorem three_dvd_sq_add (q : ℕ) (hq : 1 ≤ q) (h3 : 3 ∣ q ^ 3 - 1) : 3 ∣ q ^ 2 + q + 1 := by
  rw [cube_sub_one_eq q hq] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · obtain ⟨m, hm⟩ := h
    have hq' : q = 3 * m + 1 := by omega
    exact ⟨3 * m ^ 2 + 3 * m + 1, by rw [hq']; ring⟩
  · exact h

theorem exists_cube_root_of_fixed (hσ : orderOf σ = 3) (h3 : 3 ∣ Nat.card F - 1) {y : F}
    (hy0 : y ≠ 0) (hy : σ y = y) : ∃ μ : F, μ ^ 3 = y := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set q := Nat.card (fixF σ) with hq
  have hq2 : 2 ≤ q := two_le_card_fixF
  have hcard : Nat.card F = q ^ 3 := card_eq_cube hσ
  have hord : orderOf g = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  obtain ⟨k, hk⟩ := hg (Units.mk0 y hy0)
  have hk : g ^ k = Units.mk0 y hy0 := hk
  have hpow : g ^ (k * ((q - 1 : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, hk]
    apply Units.ext
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact pow_card_sub_one_of_fixed hy0 hy
  have hdvd : ((q ^ 3 - 1 : ℕ) : ℤ) ∣ k * ((q - 1 : ℕ) : ℤ) := by
    rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.2 hpow
  have h3' : 3 ∣ q ^ 2 + q + 1 := three_dvd_sq_add q (by omega) (hcard ▸ h3)
  have hfac : ((q ^ 3 - 1 : ℕ) : ℤ) = ((q - 1 : ℕ) : ℤ) * ((q ^ 2 + q + 1 : ℕ) : ℤ) := by
    rw [cube_sub_one_eq q (by omega), Nat.cast_mul]
  have hq1 : ((q - 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (show q - 1 ≠ 0 by omega)
  rw [hfac, mul_comm k] at hdvd
  have hdvd2 : ((q ^ 2 + q + 1 : ℕ) : ℤ) ∣ k := (mul_dvd_mul_iff_left hq1).1 hdvd
  have hk3 : (3 : ℤ) ∣ k := dvd_trans (by exact_mod_cast h3') hdvd2
  obtain ⟨m, rfl⟩ := hk3
  refine ⟨((g ^ m : Fˣ) : F), ?_⟩
  have : (g ^ m) ^ 3 = Units.mk0 y hy0 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, ← hk]
    norm_num
  have := congrArg Units.val this
  simpa using this

theorem exists_ratio_not_fixed (hσ : orderOf σ = 3) :
    ∃ a : Fˣ, σ ((a : F) / σ a) ≠ (a : F) / σ a := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_contra hall
  push Not at hall
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set q := Nat.card (fixF σ) with hq
  have hq2 : 2 ≤ q := two_le_card_fixF
  have hcard : Nat.card F = q ^ 3 := card_eq_cube hσ
  have hord : orderOf g = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have hσ3 : ∀ y : F, σ (σ (σ y)) = y := by
    intro y
    have h1 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
    have := congrArg (fun τ : F ≃+* F => τ y) h1
    simpa [pow_succ] using this
  set f : F := (g : F) / σ g with hf
  have hg0 : (g : F) ≠ 0 := g.ne_zero
  have hσg0 : σ (g : F) ≠ 0 := by simpa using hg0
  have hf0 : f ≠ 0 := div_ne_zero hg0 hσg0
  have hff : σ f = f := hall g
  have h1 : σ (g : F) = g * f⁻¹ := by rw [hf]; field_simp
  have h2 : σ (σ (g : F)) = g * f⁻¹ ^ 2 := by
    rw [h1, map_mul, h1, map_inv₀, hff]; ring
  have h3 : σ (σ (σ (g : F))) = g * f⁻¹ ^ 3 := by
    rw [h2, map_mul, h1, map_pow, map_inv₀, hff]; ring
  rw [hσ3] at h3
  have hfi : f⁻¹ ^ 3 = 1 := by
    have h' : (g : F) * f⁻¹ ^ 3 = g * 1 := by rw [mul_one]; exact h3.symm
    exact mul_left_cancel₀ hg0 h'
  have hf3 : f ^ 3 = 1 := by rw [inv_pow] at hfi; exact inv_eq_one.1 hfi
  have hg3 : σ ((g : F) ^ 3) = (g : F) ^ 3 := by
    rw [map_pow, h1, mul_pow, inv_pow, hf3, inv_one, mul_one]
  have hpow := pow_card_sub_one_of_fixed (pow_ne_zero 3 hg0) hg3
  have hdvd : q ^ 3 - 1 ∣ 3 * (q - 1) := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, pow_mul]
    exact hpow
  have hle := Nat.le_of_dvd (by omega) hdvd
  rw [cube_sub_one_eq q (by omega)] at hle
  have hq1 : 0 < q - 1 := by omega
  have : q ^ 2 + q + 1 ≤ 3 := by
    rw [mul_comm 3] at hle
    exact Nat.le_of_mul_le_mul_left hle hq1
  nlinarith

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis
