module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Q3

open scoped Pointwise commutatorElement

section Sylow

theorem exists_conj_mem_zpowers_of_orderOf_eq_three {Γ : Type*} [Group Γ] [Finite Γ]
    (h9 : ¬ 9 ∣ Nat.card Γ) {a b : Γ} (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ g : Γ, g * b * g⁻¹ ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ∣ Nat.card Γ := ha ▸ orderOf_dvd_natCard a
  have hfac : (Nat.card Γ).factorization 3 = 1 := by
    have h1 : 1 ≤ (Nat.card Γ).factorization 3 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hN).mp h3
    have h2 : ¬ 2 ≤ (Nat.card Γ).factorization 3 := fun h => h9 (by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN).mpr h
      simpa using this)
    omega
  have hP : ∀ c : Γ, orderOf c = 3 →
      Nat.card (Subgroup.zpowers c) = 3 ^ (Nat.card Γ).factorization 3 := by
    intro c hc
    rw [Nat.card_zpowers, hc, hfac]
    norm_num
  let P : Sylow 3 Γ := Sylow.ofCard (Subgroup.zpowers a) (hP a ha)
  let Q : Sylow 3 Γ := Sylow.ofCard (Subgroup.zpowers b) (hP b hb)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q P
  refine ⟨g, ?_⟩
  have hmem : g * b * g⁻¹ ∈ ((g • Q : Sylow 3 Γ) : Subgroup Γ) := by
    have hbQ : b ∈ (Q : Subgroup Γ) := Subgroup.mem_zpowers b
    have := Subgroup.smul_mem_pointwise_smul b (MulAut.conj g) _ hbQ
    rwa [MulAut.smul_def, MulAut.conj_apply] at this
  rw [hg] at hmem
  exact hmem

end Sylow

section Abstract

variable {C : Type*} [Group C] {A : Type*} [Group A]

@[expose] def centModO (ρ : C →* A) (O : Subgroup C) [O.Normal] : Subgroup C where
  carrier := {w | ∀ y ∈ ρ.ker, ⁅w, y⁆ ∈ O}
  one_mem' := fun y _ => by simp [O.one_mem]
  mul_mem' {a b} ha hb y hy := by
    have h1 : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact O.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb y hy) a) (ha y hy)
  inv_mem' {a} ha y hy := by
    have h1 : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have h2 := Subgroup.Normal.conj_mem (inferInstance : O.Normal) _ (O.inv_mem (ha y hy)) a⁻¹
    simpa using h2

theorem mem_centModO {ρ : C →* A} {O : Subgroup C} [O.Normal] {w : C} :
    w ∈ centModO ρ O ↔ ∀ y ∈ ρ.ker, ⁅w, y⁆ ∈ O := Iff.rfl

end Abstract

section Equiv

variable {C : Type*} [Group C] [Finite C] {A : Type*} [Group A]

theorem exists_centModO_of_inner (ρ : C →* A) (O : Subgroup C) [O.Normal] {x : C}
    (hx3 : ρ x ^ 3 = 1) (hx1 : ρ x ≠ 1)
    (hin : ∃ dd ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ O) :
    ∃ (x' : C) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ ρ x' ≠ 1 ∧ x' ∈ centModO ρ O := by
  obtain ⟨dd, hdd, hy⟩ := hin
  have hwO : dd⁻¹ * x ∈ centModO ρ O := by
    intro y hy'
    have h1 : ⁅dd⁻¹ * x, y⁆ = dd⁻¹ * (x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹) * dd := by
      simp only [commutatorElement_def]; group
    rw [h1]
    have := Subgroup.Normal.conj_mem (inferInstance : O.Normal) _ (hy y hy') dd⁻¹
    simpa using this
  have hρw : ρ (dd⁻¹ * x) = ρ x := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hdd, inv_one, one_mul]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (dd⁻¹ * x)).ne' 3
    (by norm_num)
  refine ⟨(dd⁻¹ * x) ^ (b * b), a, ?_, ?_, Subgroup.pow_mem _ hwO _⟩
  · rw [← pow_mul]
    have : b * b * 3 ^ a = orderOf (dd⁻¹ * x) * b := by rw [hab]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hρw]
    have hord : orderOf (ρ x) = 3 := orderOf_eq_prime hx3 hx1
    have hb3 : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have hbb : (b * b) % 3 = 1 := by rcases hb3 with h | h <;> simp [Nat.mul_mod, h]
    rw [← pow_mod_orderOf, hord, hbb, pow_one]
    exact hx1

omit [Finite C] in
theorem exists_inner_of_centModO (ρ : C →* A) (O : Subgroup C) [O.Normal]
    (h3 : ∀ (x : C) (k : ℕ), x ^ 3 ^ k = 1 → ρ x ^ 3 = 1)
    (hSyl : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, orderOf a = 3 → orderOf b = 3 →
      ∃ g ∈ ρ.range, g * b * g⁻¹ ∈ Subgroup.zpowers a)
    {x : C} {k : ℕ} (hx : x ^ 3 ^ k = 1) (hx1 : ρ x ≠ 1)
    {x' : C} {k' : ℕ} (hx' : x' ^ 3 ^ k' = 1) (hx'1 : ρ x' ≠ 1) (hW : x' ∈ centModO ρ O) :
    ∃ dd ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ O := by
  have hx3 := h3 x k hx
  have hord : orderOf (ρ x) = 3 := orderOf_eq_prime hx3 hx1
  have hord' : orderOf (ρ x') = 3 := orderOf_eq_prime (h3 x' k' hx') hx'1
  obtain ⟨g, ⟨c, rfl⟩, hg⟩ := hSyl (ρ x) ⟨x, rfl⟩ (ρ x') ⟨x', rfl⟩ hord hord'
  have hρy₀ : ρ (c * x' * c⁻¹) ∈ Subgroup.zpowers (ρ x) := by
    rw [map_mul, map_mul, map_inv]; exact hg
  have hy₀1 : ρ (c * x' * c⁻¹) ≠ 1 := by
    intro h
    apply hx'1
    rw [map_mul, map_mul, map_inv] at h
    simpa using h
  obtain ⟨e, he⟩ : ∃ e : ℕ, ρ ((c * x' * c⁻¹) ^ e) = ρ x := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hρy₀
    have hjm : (ρ x) ^ (j % (3 : ℤ)) = ρ c * ρ x' * (ρ c)⁻¹ := by
      have := zpow_mod_orderOf (ρ x) j
      rw [hord] at this
      rw [show ((3 : ℕ) : ℤ) = 3 from rfl] at this
      rw [this, hj, map_mul, map_mul, map_inv]
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj3 with h | h | h
    · exfalso
      apply hy₀1
      rw [map_mul, map_mul, map_inv, ← hjm, h, zpow_zero]
    · refine ⟨1, ?_⟩
      rw [pow_one, map_mul, map_mul, map_inv, ← hjm, h, zpow_one]
    · refine ⟨2, ?_⟩
      rw [map_pow, map_mul, map_mul, map_inv, ← hjm, h]
      have : ((ρ x) ^ (2 : ℤ)) ^ 2 = (ρ x) ^ 3 * ρ x := by
        rw [← zpow_natCast, ← zpow_mul]; rw [show ((2 : ℤ) * (((2 : ℕ)) : ℤ)) = 3 + 1 by norm_num]
        rw [zpow_add, zpow_one]; norm_cast
      rw [this, hx3, one_mul]
  have hy₀ : c * x' * c⁻¹ ∈ centModO ρ O := by
    intro y hy
    have hy' : c⁻¹ * y * c ∈ ρ.ker := by
      have := (MonoidHom.normal_ker ρ).conj_mem y hy c⁻¹
      simpa using this
    have h1 : ⁅c * x' * c⁻¹, y⁆ = c * ⁅x', c⁻¹ * y * c⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact Subgroup.Normal.conj_mem (inferInstance : O.Normal) _ (hW _ hy') c
  have hx₀ : (c * x' * c⁻¹) ^ e ∈ centModO ρ O := Subgroup.pow_mem _ hy₀ e
  have hd : ((c * x' * c⁻¹) ^ e)⁻¹ * x ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  refine ⟨((c * x' * c⁻¹) ^ e)⁻¹ * x, hd, fun y hy => ?_⟩
  have hy2 : (((c * x' * c⁻¹) ^ e)⁻¹ * x) * y * (((c * x' * c⁻¹) ^ e)⁻¹ * x)⁻¹ ∈ ρ.ker :=
    ρ.ker.mul_mem (ρ.ker.mul_mem hd hy) (ρ.ker.inv_mem hd)
  have key : x * y * x⁻¹ * ((((c * x' * c⁻¹) ^ e)⁻¹ * x) * y *
      (((c * x' * c⁻¹) ^ e)⁻¹ * x)⁻¹)⁻¹ = ⁅(c * x' * c⁻¹) ^ e,
      (((c * x' * c⁻¹) ^ e)⁻¹ * x) * y * (((c * x' * c⁻¹) ^ e)⁻¹ * x)⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [key]
  exact hx₀ _ hy2

theorem forall_exists_centModO_iff_forall_exists_inner (ρ : C →* A) (O : Subgroup C) [O.Normal]
    (h3 : ∀ (x : C) (k : ℕ), x ^ 3 ^ k = 1 → ρ x ^ 3 = 1)
    (hSyl : ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, orderOf a = 3 → orderOf b = 3 →
      ∃ g ∈ ρ.range, g * b * g⁻¹ ∈ Subgroup.zpowers a) :
    (∀ (x : C) (k : ℕ), x ^ 3 ^ k = 1 → ρ x ≠ 1 →
      ∃ (x' : C) (k' : ℕ), x' ^ 3 ^ k' = 1 ∧ ρ x' ≠ 1 ∧ x' ∈ centModO ρ O) ↔
    (∀ (x : C) (k : ℕ), x ^ 3 ^ k = 1 → ρ x ≠ 1 →
      ∃ dd ∈ ρ.ker, ∀ y ∈ ρ.ker, x * y * x⁻¹ * (dd * y * dd⁻¹)⁻¹ ∈ O) := by
  constructor
  · intro h x k hx hx1
    obtain ⟨x', k', hx', hx'1, hW⟩ := h x k hx hx1
    exact exists_inner_of_centModO ρ O h3 hSyl hx hx1 hx' hx'1 hW
  · intro h x k hx hx1
    exact exists_centModO_of_inner ρ O (h3 x k hx) hx1 (h x k hx hx1)

end Equiv

end CFSG.ClassicalInvolution.Q3
