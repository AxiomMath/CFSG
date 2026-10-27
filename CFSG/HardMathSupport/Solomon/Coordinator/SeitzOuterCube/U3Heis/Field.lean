module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalForm.Fix
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.FieldFacts
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF)

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)

theorem norm_eq_pow (u : F) : h.bar u * u = u ^ (ℓ ^ f + 1) := by
  rw [UnitaryFieldData.bar_apply, pow_succ]

variable {σ : F ≃+* F}

include h in
theorem card_fixF_eq (hσ : orderOf σ = 3) : Nat.card (fixF σ) = (ℓ ^ (f / 3)) ^ 2 := by
  obtain ⟨h₀, -⟩ := U3NF.exists_fixData h hσ
  rw [h₀.card, ← pow_mul, mul_comm]

theorem cube_add_one_eq (a : ℕ) (ha : 1 ≤ a) : a ^ 3 + 1 = (a ^ 2 - 1) * a + (a + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, a = r + 1 := ⟨a - 1, by omega⟩
  have : (r + 1) ^ 2 - 1 = r ^ 2 + 2 * r := by
    rw [show (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 by ring, Nat.add_sub_cancel]
  rw [this]
  ring

include h in
theorem one_le_q0 : 1 ≤ ℓ ^ (f / 3) := Nat.one_le_pow _ _ h.prime.pos

theorem pow_q0_succ_of_fixed (hσ : orderOf σ = 3) {u : F} (hu : σ u = u)
    (hn : h.bar u * u = 1) : u ^ (ℓ ^ (f / 3) + 1) = 1 := by
  have := h.finite
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn
    exact zero_ne_one hn
  have hA : u ^ ((ℓ ^ (f / 3)) ^ 2 - 1) = 1 := by
    rw [← card_fixF_eq h hσ]
    exact CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.A2Heis.pow_card_sub_one_of_fixed
      hu0 hu
  have hB : u ^ (ℓ ^ f + 1) = 1 := by rw [← norm_eq_pow h, hn]
  rw [U3NF.pow_eq_cube h hσ, cube_add_one_eq _ (one_le_q0 h), pow_add, pow_mul, hA, one_pow,
    one_mul] at hB
  exact hB

theorem exists_cube_factor {a : ℕ} (h3 : 3 ∣ a + 1) :
    ∃ c : ℕ, a ^ 3 + 1 = (a + 1) * (3 * c) := by
  obtain ⟨t, ht⟩ := h3
  obtain ⟨r, rfl⟩ : ∃ r, a = 3 * r + 2 := ⟨t - 1, by omega⟩
  exact ⟨3 * r ^ 2 + 3 * r + 1, by ring⟩

theorem exists_cube_root_of_fixed (hσ : orderOf σ = 3) (h3 : 3 ∣ ℓ ^ f + 1) {u : F}
    (hu : σ u = u) (hn : h.bar u * u = 1) : ∃ κ : F, κ ^ 3 = u ∧ h.bar κ * κ = 1 := by
  classical
  have := h.finite
  have : Fintype F := Fintype.ofFinite F
  set q₀ := ℓ ^ (f / 3) with hq₀
  have hq : ℓ ^ f = q₀ ^ 3 := U3NF.pow_eq_cube h hσ
  have h30 : 3 ∣ q₀ + 1 := U3NF.three_dvd_sub_data h hσ h3
  obtain ⟨c, hc⟩ := exists_cube_factor h30
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hn
    exact zero_ne_one hn
  have hpow := pow_q0_succ_of_fixed h hσ hu hn
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hq1 := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card h.card_eq_sq
  have hcard : Nat.card Fˣ = (ℓ ^ f) ^ 2 - 1 :=
    CFSG.ClassicalGroups.Unitary.card_units_of_card h.card_eq_sq
  have hfac : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [CFSG.ClassicalGroups.Unitary.sq_sub_one_eq _ hq1.le, mul_comm]
  have hgo : orderOf g = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard, hfac]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 u hu0 :=
    mem_powers_iff_mem_zpowers.2 (hg _)
  have hk1 : g ^ (k * (q₀ + 1)) = 1 := by
    rw [pow_mul, hk]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hpow, Units.val_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hk1
  rw [hgo, hq, hc] at hdvd
  have hdvd' : (q₀ ^ 3 - 1) * (3 * c) ∣ k := by
    have e : (q₀ ^ 3 - 1) * ((q₀ + 1) * (3 * c)) = (q₀ ^ 3 - 1) * (3 * c) * (q₀ + 1) := by ring
    rw [e] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
  obtain ⟨j, hj⟩ := hdvd'
  refine ⟨((g ^ ((q₀ ^ 3 - 1) * c * j) : Fˣ) : F), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul,
      show (q₀ ^ 3 - 1) * c * j * 3 = k by rw [hj]; ring, hk, Units.val_mk0]
  · rw [norm_eq_pow h, ← Units.val_pow_eq_pow_val, ← pow_mul, hq, hc,
      show (q₀ ^ 3 - 1) * c * j * ((q₀ + 1) * (3 * c)) =
        (q₀ ^ 3 - 1) * ((q₀ + 1) * (3 * c)) * (c * j) by ring, pow_mul]
    rw [hq, hc] at hgo
    rw [← hgo, pow_orderOf_eq_one, one_pow, Units.val_one]

theorem exists_gen_cube (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ z : F, h.bar z * z = 1 ∧ orderOf (z ^ 3) = (ℓ ^ f + 1) / 3 := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨l, hl, hlo⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq (F := F) (p := ℓ)
    (f := f) h.card_eq_sq
  refine ⟨(l : F), ?_, ?_⟩
  · rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hl
    rw [UnitaryFieldData.bar_apply]
    exact hl
  · have e : orderOf (l : F) = ℓ ^ f + 1 := by rw [orderOf_units, hlo]
    rw [orderOf_pow' _ (by norm_num), e, Nat.gcd_eq_right h3]

include h in
theorem five_le_q0 (hσ : orderOf σ = 3) (h3 : 3 ∣ ℓ ^ f + 1) (hq2 : 2 < ℓ ^ f)
    (hq8 : ℓ ^ f ≠ 8) : 5 ≤ ℓ ^ (f / 3) := by
  have hq := U3NF.pow_eq_cube h hσ
  have h30 := U3NF.three_dvd_sub_data h hσ h3
  rw [hq] at hq2 hq8
  by_contra hlt
  push Not at hlt
  generalize ℓ ^ (f / 3) = a at hq2 hq8 h30 hlt
  interval_cases a <;> simp_all <;> omega

include h in
theorem three_ne_zero' (h3 : 3 ∣ ℓ ^ f + 1) : (3 : F) ≠ 0 := by
  have := h.charP
  intro h0
  have hℓ : ℓ ∣ 3 := by
    have := (CharP.cast_eq_zero_iff F ℓ 3).1 (by exact_mod_cast h0)
    exact this
  have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 hℓ
  subst hℓ3
  have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
  have := (Nat.dvd_add_right h1).1 h3
  omega

theorem one_add_two_mul_ne_zero (h3 : (3 : F) ≠ 0) {s : F} (hn : h.bar s * s = 1) :
    1 + 2 * s ≠ 0 := by
  intro e1
  have e2 : 1 + 2 * h.bar s = 0 := by
    have := congrArg h.bar e1
    rwa [map_add, map_mul, map_one, map_ofNat, map_zero] at this
  exact h3 (by linear_combination (2 * h.bar s) * e1 - e2 - 4 * hn)

theorem exists_fixed_norm_one (hσ : orderOf σ = 3) (hq0 : 5 ≤ ℓ ^ (f / 3)) :
    ∃ s : F, σ s = s ∧ h.bar s * s = 1 ∧ s ^ 2 ≠ 1 ∧ s ^ 3 ≠ 1 := by
  have := h.finite
  have : Finite (fixF σ) := Subtype.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  obtain ⟨h₀, hbar⟩ := U3NF.exists_fixData h hσ
  have := h₀.charP
  obtain ⟨l, hl, hlo⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq (F := fixF σ)
    (p := ℓ) (f := f / 3) h₀.card_eq_sq
  have hcoe : ∀ n : ℕ, (((l : fixF σ) : F)) ^ n = 1 → l ^ n = 1 := by
    intro n hn
    apply Units.ext
    apply Subtype.ext
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, hn, Units.val_one]
    rfl
  refine ⟨((l : fixF σ) : F), mem_fixF.1 (l : fixF σ).2, ?_, ?_, ?_⟩
  · rw [← hbar]
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hl
    have e : h₀.bar (l : fixF σ) * (l : fixF σ) = 1 := by
      rw [UnitaryFieldData.bar_apply]; exact hl
    have := congrArg (fun x : fixF σ => (x : F)) e
    simpa using this
  · intro h2
    have := orderOf_dvd_of_pow_eq_one (hcoe 2 h2)
    rw [hlo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · intro h2
    have := orderOf_dvd_of_pow_eq_one (hcoe 3 h2)
    rw [hlo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
