module

public import CFSG.LocalAnalysis.OddStandard.ONan76Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.ONan76

open Subgroup

section Arith

variable {n : ℕ}

theorem two_mul_eq_zero_iff (hn : 1 ≤ n) (x : ZMod (2 ^ n)) :
    2 * x = 0 ↔ x = 0 ∨ x = 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hlt := ZMod.val_lt x
  obtain ⟨a, ha⟩ : ∃ a, a = x.val := ⟨_, rfl⟩
  rw [← ha] at hlt
  constructor
  · intro h
    have h1 : ((2 * a : ℕ) : ZMod (2 ^ (m + 1))) = 0 := by
      rw [Nat.cast_mul, ha, ZMod.natCast_zmod_val]
      exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    obtain ⟨k, hk⟩ := h1
    rw [pow_succ] at hk hlt
    have hak : a = 2 ^ m * k := by
      apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
      rw [hk]
      ring
    rw [hak] at hlt
    have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left hlt
    interval_cases k
    · left
      rw [mul_zero] at hak
      exact (ZMod.val_eq_zero x).mp (ha ▸ hak)
    · right
      rw [← ZMod.natCast_zmod_val x, ← ha, hak, mul_one]
      push_cast
      rfl
  · rintro (rfl | rfl)
    · rw [mul_zero]
    · rw [← pow_succ']
      exact_mod_cast ZMod.natCast_self (2 ^ (m + 1))

theorem two_pow_pred_ne_zero (hn : 1 ≤ n) : (2 : ZMod (2 ^ n)) ^ (n - 1) ≠ 0 := by
  intro h
  have h1 : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by positivity) h1
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem two_mul_two_pow_pred (hn : 1 ≤ n) : (2 : ZMod (2 ^ n)) * 2 ^ (n - 1) = 0 :=
  (two_mul_eq_zero_iff hn _).mpr (Or.inr rfl)

end Arith

section Pow

variable {G : Type*} [Group G] {n : ℕ} {v : G}

theorem pow_val_add (hv : v ^ 2 ^ n = 1) (a b : ZMod (2 ^ n)) :
    v ^ (a + b).val = v ^ a.val * v ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hv).symm

theorem pow_val_zero : v ^ (0 : ZMod (2 ^ n)).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem pow_val_neg (hv : v ^ 2 ^ n = 1) (a : ZMod (2 ^ n)) :
    v ^ (-a).val = (v ^ a.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_val_add hv, neg_add_cancel, pow_val_zero]

theorem conj_pow_inv (g x : G) (k : ℕ) : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := k)

end Pow

section Vec

variable {G : Type*} [Group G]

abbrev Vec (n : ℕ) : Type := ZMod (2 ^ n) × ZMod (2 ^ n) × ZMod (2 ^ n)

@[expose] def vec (v₁ v₂ v₃ : G) {n : ℕ} (p : Vec n) : G :=
  v₁ ^ p.1.val * v₂ ^ p.2.1.val * v₃ ^ p.2.2.val

@[expose] def actS {n : ℕ} (p : Vec n) : Vec n := (p.2.2, p.1 - p.2.2, p.2.1 + p.2.2)

@[expose] def actT {n : ℕ} (p : Vec n) : Vec n := (-p.2.2, -p.2.1, -p.1)

end Vec

namespace AlperinFrame

variable {G : Type*} [Group G] {n : ℕ} {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

abbrev V (_hF : AlperinFrame n v₁ v₂ v₃ s t) : Subgroup G := closure {v₁, v₂, v₃}

theorem c12 {a b : ℕ} : Commute (v₁ ^ a) (v₂ ^ b) := (Commute.pow_pow hF.comm₁₂ a b)
theorem c13 {a b : ℕ} : Commute (v₁ ^ a) (v₃ ^ b) := (Commute.pow_pow hF.comm₁₃ a b)
theorem c23 {a b : ℕ} : Commute (v₂ ^ a) (v₃ ^ b) := (Commute.pow_pow hF.comm₂₃ a b)

theorem vec_add (p q : Vec n) : vec v₁ v₂ v₃ (p + q) = vec v₁ v₂ v₃ p * vec v₁ v₂ v₃ q := by
  simp only [vec, Prod.fst_add, Prod.snd_add, pow_val_add hF.pow₁, pow_val_add hF.pow₂,
    pow_val_add hF.pow₃]
  have h1 := (hF.c12 (a := q.1.val) (b := p.2.1.val)).eq
  have h2 := (hF.c13 (a := q.1.val) (b := p.2.2.val)).eq
  have h3 := (hF.c23 (a := q.2.1.val) (b := p.2.2.val)).eq
  calc v₁ ^ p.1.val * v₁ ^ q.1.val * (v₂ ^ p.2.1.val * v₂ ^ q.2.1.val) *
        (v₃ ^ p.2.2.val * v₃ ^ q.2.2.val)
      = v₁ ^ p.1.val * (v₁ ^ q.1.val * v₂ ^ p.2.1.val) * (v₂ ^ q.2.1.val * v₃ ^ p.2.2.val) *
        v₃ ^ q.2.2.val := by simp only [mul_assoc]
    _ = v₁ ^ p.1.val * (v₂ ^ p.2.1.val * v₁ ^ q.1.val) * (v₃ ^ p.2.2.val * v₂ ^ q.2.1.val) *
        v₃ ^ q.2.2.val := by rw [h1, h3]
    _ = v₁ ^ p.1.val * v₂ ^ p.2.1.val * (v₁ ^ q.1.val * v₃ ^ p.2.2.val) * v₂ ^ q.2.1.val *
        v₃ ^ q.2.2.val := by simp only [mul_assoc]
    _ = v₁ ^ p.1.val * v₂ ^ p.2.1.val * (v₃ ^ p.2.2.val * v₁ ^ q.1.val) * v₂ ^ q.2.1.val *
        v₃ ^ q.2.2.val := by rw [h2]
    _ = _ := by simp only [mul_assoc]

theorem vec_zero : vec v₁ v₂ v₃ (0 : Vec n) = 1 := by
  simp only [vec, Prod.fst_zero, Prod.snd_zero, pow_val_zero, mul_one]

theorem vec_neg (p : Vec n) : vec v₁ v₂ v₃ (-p) = (vec v₁ v₂ v₃ p)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hF.vec_add, neg_add_cancel, hF.vec_zero]

theorem vec_sub (p q : Vec n) :
    vec v₁ v₂ v₃ (p - q) = vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q)⁻¹ := by
  rw [sub_eq_add_neg, hF.vec_add, hF.vec_neg]

theorem vec_nsmul (k : ℕ) (p : Vec n) : vec v₁ v₂ v₃ (k • p) = vec v₁ v₂ v₃ p ^ k := by
  induction k with
  | zero => rw [zero_smul, hF.vec_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, hF.vec_add, ih, pow_succ]

theorem vec_comm (p q : Vec n) :
    vec v₁ v₂ v₃ p * vec v₁ v₂ v₃ q = vec v₁ v₂ v₃ q * vec v₁ v₂ v₃ p := by
  rw [← hF.vec_add, ← hF.vec_add, add_comm]

theorem vec_mem_V (p : Vec n) : vec v₁ v₂ v₃ p ∈ hF.V := by
  refine mul_mem (mul_mem (pow_mem (subset_closure ?_) _) (pow_mem (subset_closure ?_) _))
    (pow_mem (subset_closure ?_) _) <;> simp

theorem vec_e1 (hn : 1 ≤ n) : vec v₁ v₂ v₃ ((1, 0, 0) : Vec n) = v₁ := by
  have : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  simp [vec, ZMod.val_one]

theorem vec_e2 (hn : 1 ≤ n) : vec v₁ v₂ v₃ ((0, 1, 0) : Vec n) = v₂ := by
  have : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  simp [vec, ZMod.val_one]

theorem vec_e3 (hn : 1 ≤ n) : vec v₁ v₂ v₃ ((0, 0, 1) : Vec n) = v₃ := by
  have : Fact (1 < 2 ^ n) := ⟨Nat.one_lt_two_pow (by omega)⟩
  simp [vec, ZMod.val_one]

theorem exists_vec_of_mem_V (hn : 1 ≤ n) {x : G} (hx : x ∈ hF.V) :
    ∃ p : Vec n, vec v₁ v₂ v₃ p = x := by
  induction hx using closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl | rfl
    · exact ⟨_, hF.vec_e1 hn⟩
    · exact ⟨_, hF.vec_e2 hn⟩
    · exact ⟨_, hF.vec_e3 hn⟩
  | one => exact ⟨0, hF.vec_zero⟩
  | mul y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    exact ⟨p + q, hF.vec_add p q⟩
  | inv y _ hy =>
    obtain ⟨p, rfl⟩ := hy
    exact ⟨-p, hF.vec_neg p⟩

theorem vec_injective (hn : 1 ≤ n) : Function.Injective (vec v₁ v₂ v₃ (n := n)) := by
  classical
  have hsurj : Function.Surjective (fun p : Vec n => (⟨vec v₁ v₂ v₃ p, hF.vec_mem_V p⟩ : hF.V)) :=
    fun x => by
      obtain ⟨p, hp⟩ := hF.exists_vec_of_mem_V hn x.2
      exact ⟨p, Subtype.ext hp⟩
  have hcard : Nat.card (Vec n) = Nat.card hF.V := by
    rw [hF.card_V]
    simp only [Nat.card_prod, Nat.card_zmod]
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hinj := (hsurj.bijective_of_nat_card_le hcard.le).1
  intro p q h
  exact hinj (Subtype.ext h)

theorem vec_eq_one_iff (hn : 1 ≤ n) {p : Vec n} : vec v₁ v₂ v₃ p = 1 ↔ p = 0 :=
  ⟨fun h => hF.vec_injective hn (h.trans hF.vec_zero.symm), fun h => h ▸ hF.vec_zero⟩

theorem vec_inj (hn : 1 ≤ n) {p q : Vec n} : vec v₁ v₂ v₃ p = vec v₁ v₂ v₃ q ↔ p = q :=
  (hF.vec_injective hn).eq_iff

theorem conj_s_pow₁ (k : ℕ) : s⁻¹ * v₁ ^ k * s = v₂ ^ k := by rw [← conj_pow_inv, hF.s_v₁]
theorem conj_s_pow₂ (k : ℕ) : s⁻¹ * v₂ ^ k * s = v₃ ^ k := by rw [← conj_pow_inv, hF.s_v₂]

theorem conj_s_pow₃ (c : ZMod (2 ^ n)) :
    s⁻¹ * v₃ ^ c.val * s = v₁ ^ c.val * v₂ ^ (-c).val * v₃ ^ c.val := by
  rw [← conj_pow_inv, hF.s_v₃, pow_val_neg hF.pow₂]
  have h1 : Commute v₁ v₂⁻¹ := Commute.inv_right hF.comm₁₂
  have h2 : Commute (v₁ * v₂⁻¹) v₃ := Commute.mul_left hF.comm₁₃ (Commute.inv_left hF.comm₂₃)
  rw [h2.mul_pow, h1.mul_pow, inv_pow]

theorem conj_s (p : Vec n) : s⁻¹ * vec v₁ v₂ v₃ p * s = vec v₁ v₂ v₃ (actS p) := by
  have e : s⁻¹ * vec v₁ v₂ v₃ p * s =
      (s⁻¹ * v₁ ^ p.1.val * s) * (s⁻¹ * v₂ ^ p.2.1.val * s) * (s⁻¹ * v₃ ^ p.2.2.val * s) := by
    simp only [vec]
    group
  rw [e, hF.conj_s_pow₁, hF.conj_s_pow₂, hF.conj_s_pow₃]
  have : vec v₁ v₂ v₃ (actS p) = vec v₁ v₂ v₃ ((0, p.1, p.2.1) + (p.2.2, -p.2.2, p.2.2)) := by
    congr 1
    simp only [actS, Prod.mk_add_mk, zero_add]
    ext <;> simp [sub_eq_add_neg, add_comm]
  rw [this, hF.vec_add]
  simp only [vec, pow_val_zero, one_mul]

theorem conj_t (p : Vec n) : t⁻¹ * vec v₁ v₂ v₃ p * t = vec v₁ v₂ v₃ (actT p) := by
  have e : t⁻¹ * vec v₁ v₂ v₃ p * t =
      (t⁻¹ * v₁ ^ p.1.val * t) * (t⁻¹ * v₂ ^ p.2.1.val * t) * (t⁻¹ * v₃ ^ p.2.2.val * t) := by
    simp only [vec]
    group
  rw [e, ← conj_pow_inv, ← conj_pow_inv, ← conj_pow_inv, hF.t_v₁, hF.t_v₂, hF.t_v₃, inv_pow,
    inv_pow, inv_pow]
  simp only [vec, actT, pow_val_neg hF.pow₁, pow_val_neg hF.pow₂, pow_val_neg hF.pow₃]
  have h1 := (hF.c13 (a := p.2.2.val) (b := p.1.val)).eq
  have h2 := (hF.c12 (a := p.2.2.val) (b := p.2.1.val)).eq
  have h3 := (hF.c23 (a := p.2.1.val) (b := p.1.val)).eq
  rw [← mul_inv_rev, ← mul_inv_rev, ← mul_inv_rev, ← mul_inv_rev]
  congr 1
  calc v₁ ^ p.2.2.val * (v₂ ^ p.2.1.val * v₃ ^ p.1.val)
      = v₁ ^ p.2.2.val * (v₃ ^ p.1.val * v₂ ^ p.2.1.val) := by rw [h3]
    _ = v₃ ^ p.1.val * (v₁ ^ p.2.2.val * v₂ ^ p.2.1.val) := by
        rw [← mul_assoc, h1, mul_assoc]
    _ = v₃ ^ p.1.val * (v₂ ^ p.2.1.val * v₁ ^ p.2.2.val) := by rw [h2]

end AlperinFrame

end CFSG.OddStandard.ONan76
