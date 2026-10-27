module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisTv

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure HeisData (p : ℕ) [NeZero p] (f : ZMod p → Module.End K V) (t ti : Module.End K V)
    (c₀ : K) : Prop where
  idem : ∀ j, f j * f j = f j
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ j, f j = 1
  t_ti : t * ti = 1
  ti_t : ti * t = 1
  tp : t ^ p = c₀ • (1 : Module.End K V)
  shift : ∀ j, t * f j = f (j + 1) * t

variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

namespace HeisData

variable (H : HeisData p f t ti c₀)

include H

theorem commute_t_ti : Commute t ti := H.t_ti.trans H.ti_t.symm

theorem ti_pow_t_pow (k : ℕ) : ti ^ k * t ^ k = 1 := by
  rw [← (H.commute_t_ti.symm).mul_pow, H.ti_t, one_pow]

theorem t_pow_ti_pow (k : ℕ) : t ^ k * ti ^ k = 1 := by
  rw [← (H.commute_t_ti).mul_pow, H.t_ti, one_pow]

theorem tpow_f (k : ℕ) (j : ZMod p) : t ^ k * f j = f (j + k) * t ^ k := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, H.shift, mul_assoc, ← pow_succ']
    push_cast
    rw [add_assoc]

theorem f_tipow (k : ℕ) (j : ZMod p) : f j * ti ^ k = ti ^ k * f (j + k) := by
  have h1 := H.tpow_f k j
  have h2 : ti ^ k * (t ^ k * f j) * ti ^ k = ti ^ k * (f (j + k) * t ^ k) * ti ^ k := by rw [h1]
  calc f j * ti ^ k = ti ^ k * (t ^ k * f j) * ti ^ k := by
        rw [← mul_assoc (ti ^ k), H.ti_pow_t_pow, one_mul]
    _ = ti ^ k * (f (j + k) * t ^ k) * ti ^ k := h2
    _ = ti ^ k * f (j + k) * (t ^ k * ti ^ k) := by simp only [mul_assoc]
    _ = ti ^ k * f (j + k) := by rw [H.t_pow_ti_pow, mul_one]

theorem tipow_f (k : ℕ) (j : ZMod p) : ti ^ k * f j = f (j - k) * ti ^ k := by
  have := H.f_tipow k (j - k)
  rw [sub_add_cancel] at this
  exact this.symm

theorem c₀_ne_zero [Nontrivial V] : c₀ ≠ 0 := by
  intro h0
  have h1 := H.tp
  rw [h0, zero_smul] at h1
  have h2 : (ti ^ p * t ^ p) = 0 := by rw [h1, mul_zero]
  rw [H.ti_pow_t_pow] at h2
  exact one_ne_zero h2

theorem ti_pow_p [Nontrivial V] : ti ^ p = c₀⁻¹ • (1 : Module.End K V) := by
  have h0 := H.c₀_ne_zero
  have h1 : ti ^ p = ti ^ p * (t ^ p * ti ^ p) := by rw [H.t_pow_ti_pow, mul_one]
  rw [h1, ← mul_assoc, H.ti_pow_t_pow, one_mul]
  have h2 : t ^ p * ti ^ p = 1 := H.t_pow_ti_pow p
  rw [H.tp, smul_mul_assoc, one_mul] at h2
  have h3 : ti ^ p = c₀⁻¹ • (c₀ • ti ^ p) := by rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
  rw [h3, h2]

theorem ti_pow_mul_t_pow_le {k l : ℕ} (h : k ≤ l) : ti ^ k * t ^ l = t ^ (l - k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← mul_assoc, H.ti_pow_t_pow, one_mul]
  simp

theorem ti_pow_mul_t_pow_ge {k l : ℕ} (h : l ≤ k) : ti ^ k * t ^ l = ti ^ (k - l) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have : ti ^ (l + m) = ti ^ m * ti ^ l := by rw [add_comm, pow_add]
  rw [this, mul_assoc, H.ti_pow_t_pow, mul_one]
  simp

end HeisData

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
