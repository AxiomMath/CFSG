module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem apply_eq_of_mem_fixed {σ : K ≃+* K} {x : K} (hx : x ∈ semilinearFixedSubfield σ) :
    σ x = x :=
  hx

theorem add_one_dvd_sq_sub_one (Q₀ : ℕ) : Q₀ + 1 ∣ Q₀ ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos Q₀ with rfl | hQ
  · simp
  · refine ⟨Q₀ - 1, ?_⟩
    have h0 : 1 ≤ Q₀ := hQ
    have h1 : 1 ≤ Q₀ ^ 2 := Nat.one_le_pow _ _ hQ
    zify [h0, h1]
    ring

theorem exists_primitiveRoot_fixed [Finite K] (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) {σ : K ≃+* K} {Q₀ : ℕ}
    (hK0 : Nat.card (semilinearFixedSubfield σ) = Q₀ ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ Q₀) (hpQ : p ∣ Q₀ + 1) :
    ∃ μ : K, σ μ = μ ∧ IsPrimitiveRoot μ p ∧ h.bar μ * μ = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K₀ := semilinearFixedSubfield σ
  have hdvd : p ∣ Nat.card K₀ˣ := by
    rw [Nat.card_units, hK0]
    exact hpQ.trans (add_one_dvd_sq_sub_one Q₀)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hprim : IsPrimitiveRoot ((u : K₀) : K) p := by
    have h1 : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
    have h2 : IsPrimitiveRoot (u : K₀) p :=
      h1.map_of_injective (f := Units.coeHom K₀) Units.val_injective
    exact h2.map_of_injective (f := K₀.subtype) Subtype.val_injective
  refine ⟨((u : K₀) : K), apply_eq_of_mem_fixed (u : K₀).2, hprim, ?_⟩
  rw [hbar _ (apply_eq_of_mem_fixed (u : K₀).2), ← pow_succ]
  exact (hprim.pow_eq_one_iff_dvd _).2 hpQ

theorem exists_norm_one_not_fixed [Finite K] (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    {Q₀ p : ℕ} (hp3 : 3 ≤ p) (hK0 : Nat.card (semilinearFixedSubfield σ) = Q₀ ^ 2)
    (hq : ℓ ^ f = Q₀ ^ p) (hQ : 2 ≤ Q₀) :
    ∃ a : K, h.bar a * a = 1 ∧ σ a ≠ a := by
  set q := ℓ ^ f with hqdef
  have hK : Nat.card K = q ^ 2 := by rw [h.card, hqdef, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hg
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ h.prime.ne_zero)
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    zify [h1, hq1]
    ring
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ Q₀ := hQ
      _ ≤ Q₀ ^ p := Nat.le_self_pow (by omega) Q₀
  have hord : orderOf (g ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [hg, hfac]; exact dvd_mul_right _ _), hg, hfac,
      Nat.mul_div_cancel_left _ (by omega)]
  set a : Kˣ := g ^ (q - 1)
  have haq : (a : K) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one, Units.val_one]
  refine ⟨a, ?_, fun hfix => ?_⟩
  · rw [UnitaryFieldData.bar_apply, ← hqdef, ← pow_succ]
    exact haq
  ·
    set K₀ := semilinearFixedSubfield σ
    have ha0 : (a : K) ≠ 0 := a.ne_zero
    let b : K₀ := ⟨a, hfix⟩
    have hb0 : b ≠ 0 := fun hb => ha0 (congrArg Subtype.val hb)
    have hcard : Nat.card K₀ˣ = Q₀ ^ 2 - 1 := by rw [Nat.card_units, hK0]
    have hbpow : (Units.mk0 b hb0) ^ (Q₀ ^ 2 - 1) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hapow : a ^ (Q₀ ^ 2 - 1) = 1 := by
      apply Units.ext
      have := congrArg (fun u : K₀ˣ => ((u : K₀) : K)) hbpow
      simpa [b] using this
    have hle := Nat.le_of_dvd (by
      have : 4 ≤ Q₀ ^ 2 := by nlinarith
      omega) (hord ▸ orderOf_dvd_of_pow_eq_one hapow)
    have hp' : Q₀ ^ 3 ≤ Q₀ ^ p := Nat.pow_le_pow_right (by omega) hp3
    have : Q₀ ^ 2 < Q₀ ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem exists_primitiveRoot_nine [Finite K] (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) {Q₀ : ℕ} (hq : ℓ ^ f = Q₀ ^ 3) (h3 : 3 ∣ Q₀ + 1) :
    ∃ lam : K, h.bar lam * lam = 1 ∧ IsPrimitiveRoot lam 9 ∧ (σ lam * lam⁻¹) ^ 3 = 1 := by
  set q := ℓ ^ f with hqdef
  have hK : Nat.card K = q ^ 2 := by rw [h.card, hqdef, ← pow_mul, mul_comm]
  have h9 : 9 ∣ q + 1 := by
    obtain ⟨k, hk⟩ := h3
    rw [hq]
    have hQ : (Q₀ : ℤ) = 3 * k - 1 := by omega
    have h9' : (9 : ℤ) ∣ (Q₀ : ℤ) ^ 3 + 1 := ⟨3 * k ^ 3 - 3 * k ^ 2 + k, by rw [hQ]; ring⟩
    exact_mod_cast h9'
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ h.prime.ne_zero)
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    zify [h1, hq1]
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hg
  have h9g : 9 ∣ orderOf g := by rw [hg, hfac]; exact h9.trans (dvd_mul_left _ _)
  have hq8 : 8 ≤ q := by
    have := Nat.le_of_dvd (by omega) h9
    omega
  have hord : orderOf (g ^ (orderOf g / 9)) = 9 :=
    orderOf_pow_orderOf_div (by rw [hg, hfac]; exact Nat.mul_ne_zero (by omega) (by omega)) h9g
  set u : Kˣ := g ^ (orderOf g / 9)
  have hprim : IsPrimitiveRoot (u : K) 9 := by
    have h1 : IsPrimitiveRoot u 9 := hord ▸ IsPrimitiveRoot.orderOf u
    exact h1.map_of_injective (f := Units.coeHom K) Units.val_injective
  refine ⟨u, ?_, hprim, ?_⟩
  · rw [UnitaryFieldData.bar_apply, ← hqdef, ← pow_succ]
    exact (hprim.pow_eq_one_iff_dvd _).2 h9
  ·
    have hσu : (σ (u : K)) ^ 9 = 1 := by rw [← map_pow, hprim.pow_eq_one, map_one]
    obtain ⟨m, hm9, hm⟩ := hprim.eq_pow_of_pow_eq_one hσu
    have hσm : ∀ n : ℕ, σ ((u : K) ^ n) = (u : K) ^ (m * n) := by
      intro n
      rw [map_pow, ← hm, ← pow_mul]
    have hcube : (u : K) ^ (m * (m * m)) = u := by
      have e : (σ ^ 3) (u : K) = u := by rw [hσ3]; rfl
      have e3 : (σ ^ 3) (u : K) = σ (σ (σ (u : K))) := rfl
      rw [e3, ← hm, hσm, hσm] at e
      simpa [mul_comm, mul_assoc, mul_left_comm] using e
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    have hdiv : 9 ∣ m * (m * m) + 8 := by
      have h1 : (u : K) ^ (m * (m * m) + 8) = 1 := by
        rw [pow_add, hcube, ← pow_succ', hprim.pow_eq_one]
      exact (hprim.pow_eq_one_iff_dvd _).1 h1
    have hm3 : 3 ∣ m + 2 := by interval_cases m <;> omega
    obtain ⟨k, hk⟩ := hm3
    have hk1 : 1 ≤ k := by omega
    have hm3' : m * 3 = 9 * (k - 1) + 3 := by omega
    rw [← hm, mul_pow, ← pow_mul, inv_pow, hm3', pow_add, pow_mul, hprim.pow_eq_one, one_pow,
      one_mul, mul_inv_cancel₀ (pow_ne_zero 3 hu0)]

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
