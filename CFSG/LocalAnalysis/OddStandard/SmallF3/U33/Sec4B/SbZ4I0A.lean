module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

@[expose] def z4iFixY (Q : Type*) [Group Q] : Subgroup (MulAut Q) where
  carrier := {σ | ∀ q : Q, q ^ 2 = 1 → σ q = q}
  mul_mem' := by
    intro a b ha hb q hq
    rw [MulAut.mul_apply, hb q hq, ha q hq]
  one_mem' := fun q _ => rfl
  inv_mem' := by
    intro a ha q hq
    have h := ha q hq
    calc a⁻¹ q = a⁻¹ (a q) := by rw [h]
      _ = q := MulAut.inv_apply_self _ _ _

private lemma z4iFixY_sq_mul_inv_sq {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a)
    (h4 : ∀ q : Q, q ^ 4 = 1) {σ : MulAut Q} (hσ : σ ∈ z4iFixY Q) (q : Q) :
    (σ q * q⁻¹) ^ 2 = 1 := by
  have hq2 : (q ^ 2) ^ 2 = 1 := by
    have h : (2 : ℕ) * 2 = 4 := rfl
    rw [← pow_mul, h, h4 q]
  have hfix : σ (q ^ 2) = q ^ 2 := hσ (q ^ 2) hq2
  rw [show (σ q * q⁻¹) ^ 2 = (σ q * σ q) * (q⁻¹ * q⁻¹) by
        rw [pow_two]
        rw [show (σ q * q⁻¹) * (σ q * q⁻¹) = σ q * (q⁻¹ * σ q) * q⁻¹ by group]
        rw [hcomm (q⁻¹) (σ q)]
        group]
  rw [show σ q * σ q = σ (q ^ 2) by rw [map_pow, pow_two]]
  rw [show q⁻¹ * q⁻¹ = (q ^ 2)⁻¹ by group]
  rw [hfix]
  group

theorem z4iFixY_conj_mem {Q : Type*} [Group Q] {σ : MulAut Q} (hσ : σ ∈ z4iFixY Q)
    (g : MulAut Q) : g * σ * g⁻¹ ∈ z4iFixY Q := by
  intro q hq
  have hq' : (g⁻¹ q) ^ 2 = 1 := by
    rw [← map_pow, hq, map_one]
  rw [MulAut.mul_apply, MulAut.mul_apply, hσ (g⁻¹ q) hq', MulAut.apply_inv_self]

theorem z4iFixY_mul_comm {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a)
    (h4 : ∀ q : Q, q ^ 4 = 1) {σ τ : MulAut Q} (hσ : σ ∈ z4iFixY Q) (hτ : τ ∈ z4iFixY Q) :
    σ * τ = τ * σ := by
  ext q
  have huσ : (σ q * q⁻¹) ^ 2 = 1 := z4iFixY_sq_mul_inv_sq hcomm h4 hσ q
  have huτ : (τ q * q⁻¹) ^ 2 = 1 := z4iFixY_sq_mul_inv_sq hcomm h4 hτ q
  have hσuτ : σ (τ q * q⁻¹) = τ q * q⁻¹ := hσ _ huτ
  have hτuσ : τ (σ q * q⁻¹) = σ q * q⁻¹ := hτ _ huσ
  rw [MulAut.mul_apply, MulAut.mul_apply]
  calc σ (τ q)
      = σ ((τ q * q⁻¹) * q) := by rw [inv_mul_cancel_right]
    _ = σ (τ q * q⁻¹) * σ q := by rw [map_mul]
    _ = (τ q * q⁻¹) * σ q := by rw [hσuτ]
    _ = (τ q * q⁻¹) * ((σ q * q⁻¹) * q) := by rw [inv_mul_cancel_right]
    _ = ((τ q * q⁻¹) * (σ q * q⁻¹)) * q := by group
    _ = ((σ q * q⁻¹) * (τ q * q⁻¹)) * q := by rw [hcomm (τ q * q⁻¹) (σ q * q⁻¹)]
    _ = (σ q * q⁻¹) * ((τ q * q⁻¹) * q) := by group
    _ = (σ q * q⁻¹) * τ q := by rw [inv_mul_cancel_right]
    _ = τ ((σ q * q⁻¹) * q) := by rw [map_mul, hτuσ]
    _ = τ (σ q) := by rw [inv_mul_cancel_right]

theorem z4iFixY_mul_self {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a)
    (h4 : ∀ q : Q, q ^ 4 = 1) {σ : MulAut Q} (hσ : σ ∈ z4iFixY Q) : σ * σ = 1 := by
  ext q
  have huσ : (σ q * q⁻¹) ^ 2 = 1 := z4iFixY_sq_mul_inv_sq hcomm h4 hσ q
  have hσu : σ (σ q * q⁻¹) = σ q * q⁻¹ := hσ _ huσ
  rw [MulAut.mul_apply]
  calc σ (σ q)
      = σ ((σ q * q⁻¹) * q) := by rw [inv_mul_cancel_right]
    _ = σ (σ q * q⁻¹) * σ q := by rw [map_mul]
    _ = (σ q * q⁻¹) * σ q := by rw [hσu]
    _ = (σ q * q⁻¹) * ((σ q * q⁻¹) * q) := by rw [inv_mul_cancel_right]
    _ = ((σ q * q⁻¹) * (σ q * q⁻¹)) * q := by group
    _ = 1 * q := by rw [← pow_two, huσ]
    _ = q := by rw [one_mul]

private def z4iDelta {A : Type*} [Group A] (E : Subgroup A) (σ : A) : ↥E → A :=
  fun e => σ * (e : A) * σ⁻¹ * (e : A)⁻¹

private lemma z4iDelta_mul {A : Type*} [Group A] (E : Subgroup A) (σ : A)
    (hnorm : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (a b : ↥E) :
    z4iDelta E σ (a * b) = z4iDelta E σ a * z4iDelta E σ b := by
  have ha : (a : A) ∈ E := a.2
  have hb : (b : A) ∈ E := b.2
  have hsb : σ * (b : A) * σ⁻¹ ∈ E := hnorm _ hb
  have hca : (a : A)⁻¹ ∈ E := inv_mem ha
  have hprod : σ * (b : A) * σ⁻¹ * (b : A)⁻¹ ∈ E := mul_mem hsb (inv_mem hb)
  have hL : z4iDelta E σ (a * b)
      = (σ * (a : A) * σ⁻¹) * (σ * (b : A) * σ⁻¹) * ((a : A) * (b : A))⁻¹ := by
    simp only [z4iDelta, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hR : z4iDelta E σ a * z4iDelta E σ b
      = (σ * (a : A) * σ⁻¹) * (a : A)⁻¹ * (σ * (b : A) * σ⁻¹) * (b : A)⁻¹ := by
    simp only [z4iDelta]
    group
  rw [hL, hR, mul_inv_rev]
  calc (σ * (a : A) * σ⁻¹) * (σ * (b : A) * σ⁻¹) * ((b : A)⁻¹ * (a : A)⁻¹)
      = (σ * (a : A) * σ⁻¹) * ((σ * (b : A) * σ⁻¹ * (b : A)⁻¹) * (a : A)⁻¹) := by
        group
    _ = (σ * (a : A) * σ⁻¹) * ((a : A)⁻¹ * (σ * (b : A) * σ⁻¹ * (b : A)⁻¹)) := by
        rw [hcomm _ hprod _ hca]
    _ = (σ * (a : A) * σ⁻¹) * (a : A)⁻¹ * (σ * (b : A) * σ⁻¹) * (b : A)⁻¹ := by
        group

private def z4iDeltaHom {A : Type*} [Group A] (E : Subgroup A) (σ : A)
    (hnorm : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) : ↥E →* A :=
  MonoidHom.mk' (z4iDelta E σ) (z4iDelta_mul E σ hnorm hcomm)

private lemma z4i_commutator_le_range {A : Type*} [Group A] (E : Subgroup A) (σ : A)
    (hσ3 : σ ^ 3 = 1) (hnorm : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E)
    (hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    ⁅E, zpowers σ⁆ ≤ (z4iDeltaHom E σ hnorm hcomm).range := by
  rw [commutator_le]
  intro e he g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [zpow_eq_zpow_emod' n hσ3]
  have hn0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg n (by norm_num)
  have hn3 : n % ((3 : ℕ) : ℤ) < ((3 : ℕ) : ℤ) := Int.emod_lt_of_pos n (by norm_num)
  have hn : n % ((3 : ℕ) : ℤ) = 0 ∨ n % ((3 : ℕ) : ℤ) = 1 ∨
      n % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hn with h | h | h
  · rw [h, zpow_zero]
    refine ⟨1, ?_⟩
    rw [map_one, commutatorElement_def]
    simp
  · rw [h, zpow_one]
    refine ⟨⟨e⁻¹, inv_mem he⟩, ?_⟩
    rw [commutatorElement_def]
    have hb : σ * e⁻¹ * σ⁻¹ ∈ E := hnorm _ (inv_mem he)
    calc (z4iDeltaHom E σ hnorm hcomm) ⟨e⁻¹, inv_mem he⟩
        = (σ * e⁻¹ * σ⁻¹) * e := by
          simp only [z4iDeltaHom, z4iDelta, MonoidHom.mk'_apply, Subgroup.coe_mk,
            Subgroup.coe_inv, inv_inv]
      _ = e * (σ * e⁻¹ * σ⁻¹) := hcomm _ hb _ he
      _ = e * σ * e⁻¹ * σ⁻¹ := by group
  · rw [h, zpow_two, ← pow_two]
    refine ⟨⟨σ * e⁻¹ * σ⁻¹, hnorm _ (inv_mem he)⟩ * ⟨e⁻¹, inv_mem he⟩, ?_⟩
    have ha1 : σ * e⁻¹ * σ⁻¹ ∈ E := hnorm _ (inv_mem he)
    have hb : σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹ ∈ E := by
      have hh := hnorm (σ * e⁻¹ * σ⁻¹) ha1
      rw [show σ * (σ * e⁻¹ * σ⁻¹) * σ⁻¹ = σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹ by
            rw [pow_two]; group] at hh
      exact hh
    have hcomm2 : ⁅e, σ ^ 2⁆ = σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹ * e := by
      rw [commutatorElement_def]
      calc e * σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹
          = e * (σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹) := by group
        _ = (σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹) * e := (hcomm _ hb _ he).symm
        _ = σ ^ 2 * e⁻¹ * (σ ^ 2)⁻¹ * e := rfl
    rw [map_mul, hcomm2]
    simp only [z4iDeltaHom, z4iDelta, MonoidHom.mk'_apply, Subgroup.coe_mk, Subgroup.coe_inv,
      inv_inv]
    rw [pow_two]
    group

theorem z4i_fix_trivial {A : Type*} [Group A] (E : Subgroup A) (σ : A) (hσ3 : σ ^ 3 = 1)
    (hnorm : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E) (hcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hsq : ∀ e ∈ E, e * e = 1) {k : A} (hk : k ∈ ⁅E, zpowers σ⁆)
    (hfix : σ * k * σ⁻¹ = k) : k = 1 := by
  have hD : ⁅E, zpowers σ⁆ ≤ (z4iDeltaHom E σ hnorm hcomm).range :=
    z4i_commutator_le_range E σ hσ3 hnorm hcomm
  obtain ⟨x, hx⟩ := hD hk
  let e : A := (x : A)
  have he : e ∈ E := x.2
  let e1 : A := σ * e * σ⁻¹
  have he1 : e1 ∈ E := hnorm e he
  let e2 : A := σ * e1 * σ⁻¹
  have he2 : e2 ∈ E := hnorm e1 he1
  have hk_eq : k = e1 * e⁻¹ := by
    rw [← hx]
    rfl
  have hfix' : e2 * e1⁻¹ = e1 * e⁻¹ := by
    have hthis := hfix
    rw [hk_eq] at hthis
    have hL : σ * (e1 * e⁻¹) * σ⁻¹ = e2 * e1⁻¹ := by
      show σ * ((σ * e * σ⁻¹) * e⁻¹) * σ⁻¹
          = (σ * (σ * e * σ⁻¹) * σ⁻¹) * (σ * e * σ⁻¹)⁻¹
      group
    rw [hL] at hthis
    exact hthis
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hsq e he)
  have he1_inv : e1⁻¹ = e1 := inv_eq_of_mul_eq_one_right (hsq e1 he1)
  have he2_eq : e2 = e := by
    have h1 : e2 * e1 = e1 * e := by
      have hthis := hfix'
      rwa [he1_inv, he_inv] at hthis
    have h2 : e2 * e1 = e1 * e2 := hcomm e2 he2 e1 he1
    rw [h2] at h1
    exact mul_left_cancel h1
  have he1_eq : e1 = e := by
    have h1 : σ * e2 * σ⁻¹ = e := by
      show σ * (σ * (σ * e * σ⁻¹) * σ⁻¹) * σ⁻¹ = e
      have hσ3' : σ * σ * σ = 1 := by
        rw [← pow_two, ← pow_succ]
        exact hσ3
      calc σ * (σ * (σ * e * σ⁻¹) * σ⁻¹) * σ⁻¹
          = (σ * σ * σ) * e * (σ * σ * σ)⁻¹ := by group
        _ = e := by rw [hσ3']; group
    calc e1 = σ * e * σ⁻¹ := rfl
      _ = σ * e2 * σ⁻¹ := by rw [he2_eq]
      _ = e := h1
  rw [hk_eq, he1_eq, he_inv]
  exact hsq e he

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
