module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27OrdersArith

public section

namespace CFSG.OddStandard.Seitz77

theorem oddCore_card_modEq_card_fixed {α : Type*} [Finite α] (f : α → α) (p : ℕ) [Fact p.Prime]
    (hf : f^[p] = id) : Nat.card α ≡ Nat.card {a // f a = a} [MOD p] := by
  classical
  have := Fintype.ofFinite α
  have h := Equiv.Perm.card_fixedPoints_modEq (f := (f : Function.End α)) (p := p) (n := 1)
    (by rw [pow_one]; exact hf)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

theorem oddCore_card_submodule_modEq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (p : ℕ) [Fact p.Prime] (g : V →ₗ[ZMod 2] V) (hg : g ^ p = 1)
    (Y : Submodule (ZMod 2) V) (hY : ∀ y ∈ Y, g y ∈ Y) :
    Nat.card Y ≡ Nat.card ↥(Y ⊓ LinearMap.ker (g - 1)) [MOD p] := by
  let f : Y → Y := fun y => ⟨g y, hY y y.2⟩
  have hit : ∀ n : ℕ, ∀ y : Y, ((f^[n] y : Y) : V) = (g ^ n) y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', Module.End.mul_apply, ← ih]
  have hf : f^[p] = id := by
    funext y
    apply Subtype.ext
    rw [hit, hg]
    simp
  have h := oddCore_card_modEq_card_fixed f p hf
  have e : {y : Y // f y = y} ≃ ↥(Y ⊓ LinearMap.ker (g - 1)) :=
    { toFun := fun y => ⟨y.1.1, y.1.2, by
        have := congrArg Subtype.val y.2
        simpa [f, sub_eq_zero] using this⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, by
        apply Subtype.ext
        have := z.2.2
        simpa [f, sub_eq_zero] using this⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rwa [Nat.card_congr e] at h

theorem oddCore_eq_bot_or_eq_top_of_pow_seventeen {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (hV : Module.finrank (ZMod 2) V = 8) (g : V →ₗ[ZMod 2] V) (hg : g ^ 17 = 1)
    (hg1 : g ≠ 1) (Y : Submodule (ZMod 2) V) (hY : ∀ y ∈ Y, g y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hcard : ∀ W : Submodule (ZMod 2) V, Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    intro W
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : ∀ W : Submodule (ZMod 2) V, Module.finrank (ZMod 2) W ≤ 8 := fun W =>
    hV ▸ Submodule.finrank_le W
  have key : ∀ d : ℕ, d ≤ 8 → 2 ^ d % 17 = 1 → d = 0 ∨ d = 8 := by decide
  have hF : LinearMap.ker (g - 1) = ⊥ := by
    have h := oddCore_card_submodule_modEq 17 g hg ⊤ (fun _ _ => Submodule.mem_top)
    rw [top_inf_eq, hcard, hcard, finrank_top, hV] at h
    have h2 : 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (g - 1)) % 17 = 1 := by
      have := h.symm
      unfold Nat.ModEq at this
      omega
    rcases key _ (hle _) h2 with h0 | h8
    · exact Submodule.finrank_eq_zero.mp h0
    · exfalso
      have htop : LinearMap.ker (g - 1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (h8.trans hV.symm)
      rw [LinearMap.ker_eq_top] at htop
      exact hg1 (sub_eq_zero.mp htop)
  have h := oddCore_card_submodule_modEq 17 g hg Y hY
  rw [hF, inf_bot_eq, hcard, hcard ⊥] at h
  have h2 : 2 ^ Module.finrank (ZMod 2) Y % 17 = 1 := by
    unfold Nat.ModEq at h
    simpa using h
  rcases key _ (hle _) h2 with h0 | h8
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (h8.trans hV.symm))

theorem oddCore_dvd_card_sub_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (p : ℕ) [Fact p.Prime] (g : V →ₗ[ZMod 2] V) (hg : g ^ p = 1)
    (Y : Submodule (ZMod 2) V) (hY : ∀ y ∈ Y, g y ∈ Y)
    (hfix : Y ⊓ LinearMap.ker (g - 1) = ⊥) : p ∣ 2 ^ Module.finrank (ZMod 2) Y - 1 := by
  have h := oddCore_card_submodule_modEq p g hg Y hY
  rw [hfix] at h
  have hc : ∀ W : Submodule (ZMod 2) V, Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    intro W
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hc, hc ⊥, finrank_bot, pow_zero] at h
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h.symm

theorem oddCore_card_units_end {C : Type*} [AddCommGroup C] [Module (ZMod 2) C]
    [Module.Finite (ZMod 2) C] (a : ℕ) (h : Module.finrank (ZMod 2) C = a) :
    Nat.card (Module.End (ZMod 2) C)ˣ = ∏ i ∈ Finset.range a, (2 ^ a - 2 ^ i) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) C h
  have e : Nat.card (Matrix.GeneralLinearGroup (Fin a) (ZMod 2)) =
      Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) C) :=
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv
  rw [Matrix.card_GL_field a] at e
  simp only [ZMod.card] at e
  rw [Fin.prod_univ_eq_prod_range (fun i => 2 ^ a - 2 ^ i) a] at e
  exact e.symm

theorem oddCore_eq_of_dvd_gl (a b : ℕ) (hab : a + b = 8)
    (h : 25 ∣ (∏ i ∈ Finset.range a, (2 ^ a - 2 ^ i)) * ∏ i ∈ Finset.range b, (2 ^ b - 2 ^ i)) :
    a = 0 ∨ a = 4 ∨ a = 8 := by
  have ha : a ≤ 8 := by omega
  obtain rfl : b = 8 - a := by omega
  interval_cases a <;> simp_all [Finset.prod_range_succ]

theorem oddCore_card_gl_eight :
    Nat.card (GL (Fin 8) (ZMod 2)) = 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 :=
  CFSG.OddStandard.Seitz77.card_GL8_two

theorem oddCore_dvd_R_of_mul_dvd_gl_A {k : ℕ} (hk : Odd k)
    (h : 4080 * k ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) :
    k ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
  have h1 : 4080 * k ∣ 4080 * (2 ^ 24 * (3 ^ 4 * 5 * 7 ^ 2 * 31 * 127)) := by
    have e : 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 =
        4080 * (2 ^ 24 * (3 ^ 4 * 5 * 7 ^ 2 * 31 * 127)) := by norm_num
    rwa [e] at h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4080) h1
  have hc : Nat.Coprime k (2 ^ 24) := Nat.Coprime.pow_right 24 hk.coprime_two_right
  exact hc.dvd_of_dvd_mul_left h2

theorem oddCore_dvd_R_of_mul_dvd_gl_B {k : ℕ} (hk : Odd k)
    (h : 3600 * k ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) :
    k ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := by
  have h1 : 3600 * k ∣ 3600 * (2 ^ 24 * (3 ^ 3 * 7 ^ 2 * 17 * 31 * 127)) := by
    have e : 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 =
        3600 * (2 ^ 24 * (3 ^ 3 * 7 ^ 2 * 17 * 31 * 127)) := by norm_num
    rwa [e] at h
  have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3600) h1
  have hc : Nat.Coprime k (2 ^ 24) := Nat.Coprime.pow_right 24 hk.coprime_two_right
  exact hc.dvd_of_dvd_mul_left h2

theorem oddCore_prime_dvd_R_A {p : ℕ} (hp : p.Prime) (h : p ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 ∨ p = 127 := by
  have e : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl (e 3 (by norm_num) (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl (e 5 (by norm_num) h))
      · exact Or.inr (Or.inr (Or.inl (e 7 (by norm_num) (hp.dvd_of_dvd_pow h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (e 31 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (e 127 (by norm_num) h))))

theorem oddCore_prime_pow_mod_seventeen {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j)
    (h : p ^ j ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127) : p ^ j % 17 ≠ 1 := by
  have hpR : p ∣ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := (dvd_pow_self p (by omega)).trans h
  have hle : p ^ j ≤ 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := Nat.le_of_dvd (by norm_num) h
  rcases oddCore_prime_dvd_R_A hp hpR with rfl | rfl | rfl | rfl | rfl
  · have : j < 17 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
      (lt_of_le_of_lt hle (by norm_num))
    interval_cases j <;> simp_all
  · have : j < 12 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp
      (lt_of_le_of_lt hle (by norm_num))
    interval_cases j <;> simp_all
  · have : j < 10 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 7)).mp
      (lt_of_le_of_lt hle (by norm_num))
    interval_cases j <;> simp_all
  · have : j < 6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 31)).mp
      (lt_of_le_of_lt hle (by norm_num))
    interval_cases j <;> simp_all
  · have : j < 4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 127)).mp
      (lt_of_le_of_lt hle (by norm_num))
    interval_cases j <;> simp_all

theorem oddCore_prime_dvd_R_B {p : ℕ} (hp : p.Prime) (h : p ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127) :
    p = 3 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  have e : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl (e 3 (by norm_num) (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl (e 7 (by norm_num) (hp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr (Or.inl (e 17 (by norm_num) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (e 31 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (e 127 (by norm_num) h))))

theorem oddCore_prime_pow_dvd_R_B {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j)
    (h : p ^ j ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127) :
    (p = 31 ∧ j = 1) ∨ (p ≠ 31 ∧ p ^ j % 5 ≠ 1) := by
  have hpR : p ∣ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := (dvd_pow_self p (by omega)).trans h
  have hle : p ^ j ≤ 3 ^ 3 * 7 ^ 2 * 17 * 31 * 127 := Nat.le_of_dvd (by norm_num) h
  rcases oddCore_prime_dvd_R_B hp hpR with rfl | rfl | rfl | rfl | rfl
  · have : j < 17 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp
      (lt_of_le_of_lt hle (by norm_num))
    right
    interval_cases j <;> simp_all
  · have : j < 10 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 7)).mp
      (lt_of_le_of_lt hle (by norm_num))
    right
    interval_cases j <;> simp_all
  · have : j < 7 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 17)).mp
      (lt_of_le_of_lt hle (by norm_num))
    right
    interval_cases j <;> simp_all
  · have : j < 6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 31)).mp
      (lt_of_le_of_lt hle (by norm_num))
    left
    refine ⟨rfl, ?_⟩
    interval_cases j <;> simp_all
  · have : j < 4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 127)).mp
      (lt_of_le_of_lt hle (by norm_num))
    right
    interval_cases j <;> simp_all

end CFSG.OddStandard.Seitz77
