module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

theorem comm_pow_pow_mul {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) (m n p q : ℕ) :
    a ^ m * b ^ n * (a ^ p * b ^ q) = a ^ (m + p) * b ^ (n + q) := by
  have hc : Commute a b := hab
  have h1 : b ^ n * a ^ p = a ^ p * b ^ n := (Commute.pow_pow hc p n).eq.symm
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ n), h1]
  group

theorem eq_of_dvd_add_sub' {r i i' : ℕ} (hi : i < r) (hi' : i' < r) (h : r ∣ i + (r - i')) :
    i = i' := by
  obtain ⟨k, hk⟩ := h
  have h1 : r * k < r * 2 := by omega
  have h2 : k < 2 := Nat.lt_of_mul_lt_mul_left h1
  have h3 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have : k = 1 := by omega
  subst this
  omega

theorem exists_basis_elemAbelian {G : Type*} [Group G] {r : ℕ} (hr : r.Prime) (V : Subgroup G)
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, (∀ i j : ℕ, v₁ ^ i * v₂ ^ j = 1 → r ∣ i ∧ r ∣ j) ∧
      ∀ v ∈ V, ∃ i j : ℕ, v = v₁ ^ i * v₂ ^ j := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hr0 : 0 < r := hr.pos
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hr.ne_zero)
  have : Fintype V := Fintype.ofFinite V
  have hnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hVc]
    exact Nat.one_lt_pow two_ne_zero hr.one_lt
  obtain ⟨⟨v₁, hv₁⟩, hv₁1⟩ := exists_ne (1 : V)
  have hv₁1' : v₁ ≠ 1 := fun h => hv₁1 (Subtype.ext h)
  have ho₁ : orderOf v₁ = r := orderOf_eq_prime (hVe v₁ hv₁) hv₁1'
  have hnle : ¬ V ≤ Subgroup.zpowers v₁ := by
    intro hle
    have hzfin : Finite (Subgroup.zpowers v₁) :=
      Finite.of_injective (Subgroup.inclusion ((Subgroup.zpowers_le (H := V)).2 hv₁))
        (Subgroup.inclusion_injective _)
    have := Subgroup.card_le_of_le hle
    rw [hVc, Nat.card_zpowers, ho₁] at this
    have h2 : r < r ^ 2 := by
      calc r = r ^ 1 := (pow_one r).symm
        _ < r ^ 2 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
    omega
  obtain ⟨v₂, hv₂, hv₂n⟩ : ∃ v₂ ∈ V, v₂ ∉ Subgroup.zpowers v₁ := by
    by_contra hcon
    push Not at hcon
    exact hnle hcon
  have hc : v₁ * v₂ = v₂ * v₁ := hVab v₁ hv₁ v₂ hv₂
  have hind : ∀ i j : ℕ, v₁ ^ i * v₂ ^ j = 1 → r ∣ i ∧ r ∣ j := by
    intro i j h
    have hj : r ∣ j := by
      by_contra hj
      have hcop : Nat.Coprime j r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hj).symm
      obtain ⟨j', -, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
      have hv₂j : v₂ ^ j = (v₁ ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
      have hv₂eq : v₂ ^ (j * j') = v₂ := by
        have := Nat.div_add_mod (j * j') r
        rw [hj'] at this
        rw [← this, pow_add, pow_mul, hVe v₂ hv₂, one_pow, one_mul, pow_one]
      apply hv₂n
      rw [← hv₂eq, pow_mul, hv₂j]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers v₁) i)) j'
    obtain ⟨k, rfl⟩ := hj
    have h1 : v₂ ^ (r * k) = 1 := by rw [pow_mul, hVe v₂ hv₂, one_pow]
    rw [h1, mul_one] at h
    exact ⟨ho₁ ▸ orderOf_dvd_of_pow_eq_one h, dvd_mul_right r k⟩
  refine ⟨v₁, hv₁, v₂, hv₂, hind, ?_⟩
  let f : Fin r × Fin r → V := fun ij =>
    ⟨v₁ ^ (ij.1 : ℕ) * v₂ ^ (ij.2 : ℕ), V.mul_mem (V.pow_mem hv₁ _) (V.pow_mem hv₂ _)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : v₁ ^ (i : ℕ) * v₂ ^ (j : ℕ) = v₁ ^ (i' : ℕ) * v₂ ^ (j' : ℕ) :=
      congrArg Subtype.val h
    have h2 : v₁ ^ ((i : ℕ) + (r - i')) * v₂ ^ ((j : ℕ) + (r - j')) = 1 := by
      rw [← comm_pow_pow_mul hc, h1, comm_pow_pow_mul hc]
      have e1 : (i' : ℕ) + (r - i') = r := by omega
      have e2 : (j' : ℕ) + (r - j') = r := by omega
      rw [e1, e2, ← ho₁, pow_orderOf_eq_one, one_mul]
      rw [ho₁]
      exact hVe v₂ hv₂
    obtain ⟨d1, d2⟩ := hind _ _ h2
    have e1 := eq_of_dvd_add_sub' i.isLt i'.isLt d1
    have e2 := eq_of_dvd_add_sub' j.isLt j'.isLt d2
    ext <;> simp_all
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [← Nat.card_eq_fintype_card, hVc, sq]
  intro v hv
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨v, hv⟩
  exact ⟨i, j, (congrArg Subtype.val hij).symm⟩

end CFSG.GH74.GLS.Stage2.OddAut
