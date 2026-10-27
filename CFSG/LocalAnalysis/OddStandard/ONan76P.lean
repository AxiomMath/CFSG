module

public import CFSG.LocalAnalysis.OddStandard.ONan76Coord
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.ONan76

open Subgroup

@[expose] def actS' {n : ℕ} (p : Vec n) : Vec n := (p.1 + p.2.1, p.2.2 - p.1, p.1)

theorem actS_actS' {n : ℕ} (p : Vec n) : actS (actS' p) = p := by
  ext <;> simp only [actS, actS'] <;> ring

theorem two_pow_pred_add_self {n : ℕ} (hn : 1 ≤ n) :
    (2 : ZMod (2 ^ n)) ^ (n - 1) + 2 ^ (n - 1) = 0 := by
  rw [← two_mul]
  exact two_mul_two_pow_pred hn

theorem neg_two_pow_pred {n : ℕ} (hn : 1 ≤ n) : -(2 : ZMod (2 ^ n)) ^ (n - 1) = 2 ^ (n - 1) := by
  rw [neg_eq_iff_add_eq_zero]
  exact two_pow_pred_add_self hn

@[expose] def act {n : ℕ} (i e : ℕ) (p : Vec n) : Vec n := actT^[e] (actS^[i] p)

section act

variable {n : ℕ} (p : Vec n)

theorem act_00 : act 0 0 p = p := rfl
theorem act_10 : act 1 0 p = actS p := rfl
theorem act_20 : act 2 0 p = actS (actS p) := rfl
theorem act_30 : act 3 0 p = actS (actS (actS p)) := rfl
theorem act_01 : act 0 1 p = actT p := rfl
theorem act_11 : act 1 1 p = actT (actS p) := rfl
theorem act_21 : act 2 1 p = actT (actS (actS p)) := rfl
theorem act_31 : act 3 1 p = actT (actS (actS (actS p))) := rfl

end act

namespace AlperinFrame

variable {G : Type*} [Group G] {n : ℕ} {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

abbrev P (_hF : AlperinFrame n v₁ v₂ v₃ s t) : Subgroup G := closure {v₁, v₂, v₃, s, t}

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hF.t_sq

theorem s_mul_vec (p : Vec n) : s * vec v₁ v₂ v₃ p = vec v₁ v₂ v₃ (actS' p) * s := by
  have h := hF.conj_s (actS' p)
  rw [actS_actS'] at h
  rw [← h]
  group

theorem sinv_mul_vec (p : Vec n) : s⁻¹ * vec v₁ v₂ v₃ p = vec v₁ v₂ v₃ (actS p) * s⁻¹ := by
  rw [← hF.conj_s p]
  group

theorem t_mul_vec (p : Vec n) : t * vec v₁ v₂ v₃ p = vec v₁ v₂ v₃ (actT p) * t := by
  have h := hF.conj_t p
  rw [hF.t_inv] at h
  rw [← h, mul_assoc _ t t, hF.t_sq, mul_one]

theorem t_mul_zpow_s (i : ℤ) : t * s ^ i = s ^ (-i) * t := by
  have h : t⁻¹ * s ^ i * t = s ^ (-i) := by
    have h1 := conj_zpow (a := t⁻¹) (b := s) (i := i)
    rw [inv_inv] at h1
    rw [← h1, hF.t_s, inv_zpow']
  rw [hF.t_inv] at h
  calc t * s ^ i = t * s ^ i * t * t := by rw [mul_assoc _ t t, hF.t_sq, mul_one]
    _ = s ^ (-i) * t := by rw [h]

theorem t_mul_pow_s (i : ℕ) : t * s ^ i = (s ^ i)⁻¹ * t := by
  have h := hF.t_mul_zpow_s i
  rwa [zpow_natCast, zpow_neg, zpow_natCast] at h

theorem s_four_mem_V : s ^ 4 ∈ hF.V := by
  rcases hF.s_four with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem V_le_P : hF.V ≤ hF.P :=
  closure_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)

theorem s_mem_P : s ∈ hF.P := subset_closure (by simp)

theorem t_mem_P : t ∈ hF.P := subset_closure (by simp)

theorem vec_neg_e1 (hn : 1 ≤ n) : vec v₁ v₂ v₃ (-((1, 0, 0) : Vec n)) = v₁⁻¹ := by
  rw [hF.vec_neg, hF.vec_e1 hn]

theorem vec_neg_e2 (hn : 1 ≤ n) : vec v₁ v₂ v₃ (-((0, 1, 0) : Vec n)) = v₂⁻¹ := by
  rw [hF.vec_neg, hF.vec_e2 hn]

theorem vec_neg_e3 (hn : 1 ≤ n) : vec v₁ v₂ v₃ (-((0, 0, 1) : Vec n)) = v₃⁻¹ := by
  rw [hF.vec_neg, hF.vec_e3 hn]

theorem exists_nf_zpow (hn : 1 ≤ n) {x : G} (hx : x ∈ hF.P) :
    ∃ (p : Vec n) (i : ℤ) (e : ℕ), x = vec v₁ v₂ v₃ p * s ^ i * t ^ e := by
  induction hx using closure_induction_left with
  | one => exact ⟨0, 0, 0, by rw [hF.vec_zero, zpow_zero, pow_zero, mul_one, mul_one]⟩
  | mul_left y hy z _ ih =>
    obtain ⟨p, i, e, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h | h <;> rw [h]
    · exact ⟨(1, 0, 0) + p, i, e, by rw [hF.vec_add, hF.vec_e1 hn]; group⟩
    · exact ⟨(0, 1, 0) + p, i, e, by rw [hF.vec_add, hF.vec_e2 hn]; group⟩
    · exact ⟨(0, 0, 1) + p, i, e, by rw [hF.vec_add, hF.vec_e3 hn]; group⟩
    · refine ⟨actS' p, 1 + i, e, ?_⟩
      rw [zpow_one_add]
      simp only [← mul_assoc]
      rw [hF.s_mul_vec]
    · refine ⟨actT p, -i, e + 1, ?_⟩
      simp only [← mul_assoc]
      rw [hF.t_mul_vec, mul_assoc (vec v₁ v₂ v₃ (actT p)) t, hF.t_mul_zpow_s, pow_succ']
      simp only [mul_assoc]
  | inv_mul_cancel y hy z _ ih =>
    obtain ⟨p, i, e, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h | h <;> rw [h]
    · exact ⟨-(1, 0, 0) + p, i, e, by rw [hF.vec_add, hF.vec_neg_e1 hn]; group⟩
    · exact ⟨-(0, 1, 0) + p, i, e, by rw [hF.vec_add, hF.vec_neg_e2 hn]; group⟩
    · exact ⟨-(0, 0, 1) + p, i, e, by rw [hF.vec_add, hF.vec_neg_e3 hn]; group⟩
    · refine ⟨actS p, -1 + i, e, ?_⟩
      rw [zpow_add, zpow_neg_one]
      simp only [← mul_assoc]
      rw [hF.sinv_mul_vec]
    · refine ⟨actT p, -i, e + 1, ?_⟩
      rw [hF.t_inv]
      simp only [← mul_assoc]
      rw [hF.t_mul_vec, mul_assoc (vec v₁ v₂ v₃ (actT p)) t, hF.t_mul_zpow_s, pow_succ']
      simp only [mul_assoc]

theorem exists_nf (hn : 1 ≤ n) {x : G} (hx : x ∈ hF.P) :
    ∃ p : Vec n, ∃ i < 4, ∃ e < 2, x = vec v₁ v₂ v₃ p * s ^ i * t ^ e := by
  obtain ⟨p, i, e, rfl⟩ := hF.exists_nf_zpow hn hx
  have hi : i = 4 * (i / 4) + ((i % 4).toNat : ℤ) := by omega
  have hr : (i % 4).toNat < 4 := by omega
  have hq : (s ^ 4) ^ (i / 4) ∈ hF.V := zpow_mem hF.s_four_mem_V _
  obtain ⟨σ, hσ⟩ := hF.exists_vec_of_mem_V hn hq
  have ht : t ^ e = t ^ (e % 2) := pow_eq_pow_mod e (by rw [pow_two, hF.t_sq])
  refine ⟨p + σ, (i % 4).toNat, hr, e % 2, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [hF.vec_add, hσ, ht]
  conv_lhs => rw [hi, zpow_add, zpow_mul, zpow_natCast]
  group

theorem card_P_le [Finite G] (hn : 1 ≤ n) : Nat.card hF.P ≤ 8 * Nat.card hF.V := by
  classical
  have hsurj : Function.Surjective
      (fun x : hF.V × Fin 4 × Fin 2 => (⟨(x.1 : G) * s ^ (x.2.1 : ℕ) * t ^ (x.2.2 : ℕ),
        mul_mem (mul_mem (hF.V_le_P x.1.2) (pow_mem hF.s_mem_P _))
          (pow_mem hF.t_mem_P _)⟩ : hF.P)) := by
    rintro ⟨x, hx⟩
    obtain ⟨p, i, hi, e, he, rfl⟩ := hF.exists_nf hn hx
    exact ⟨(⟨_, hF.vec_mem_V p⟩, ⟨i, hi⟩, ⟨e, he⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin] at this
  omega

theorem conj_s_pow (i : ℕ) (p : Vec n) :
    (s ^ i)⁻¹ * vec v₁ v₂ v₃ p * s ^ i = vec v₁ v₂ v₃ (actS^[i] p) := by
  induction i with
  | zero => rw [pow_zero, inv_one, one_mul, mul_one]; rfl
  | succ i ih =>
    rw [pow_succ, Function.iterate_succ_apply', ← hF.conj_s, ← ih]
    group

theorem conj_t_pow (e : ℕ) (p : Vec n) :
    (t ^ e)⁻¹ * vec v₁ v₂ v₃ p * t ^ e = vec v₁ v₂ v₃ (actT^[e] p) := by
  induction e with
  | zero => rw [pow_zero, inv_one, one_mul, mul_one]; rfl
  | succ e ih =>
    rw [pow_succ, Function.iterate_succ_apply', ← hF.conj_t, ← ih]
    group

theorem conj_nf (q p : Vec n) (i e : ℕ) :
    (vec v₁ v₂ v₃ q * s ^ i * t ^ e)⁻¹ * vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q * s ^ i * t ^ e) =
      vec v₁ v₂ v₃ (act i e p) := by
  have h : (vec v₁ v₂ v₃ q)⁻¹ * vec v₁ v₂ v₃ p * vec v₁ v₂ v₃ q = vec v₁ v₂ v₃ p := by
    rw [mul_assoc, ← hF.vec_comm q p, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (vec v₁ v₂ v₃ q * s ^ i * t ^ e)⁻¹ * vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q * s ^ i * t ^ e)
      = (t ^ e)⁻¹ * ((s ^ i)⁻¹ * ((vec v₁ v₂ v₃ q)⁻¹ * vec v₁ v₂ v₃ p * vec v₁ v₂ v₃ q) *
          s ^ i) * t ^ e := by group
    _ = vec v₁ v₂ v₃ (act i e p) := by rw [h, hF.conj_s_pow, hF.conj_t_pow]; rfl

theorem conj_mem_V (hn : 1 ≤ n) {x v : G} (hx : x ∈ hF.P) (hv : v ∈ hF.V) :
    x⁻¹ * v * x ∈ hF.V := by
  obtain ⟨p, i, -, e, -, rfl⟩ := hF.exists_nf hn hx
  obtain ⟨q, rfl⟩ := hF.exists_vec_of_mem_V hn hv
  rw [hF.conj_nf]
  exact hF.vec_mem_V _

theorem V_comm (hn : 1 ≤ n) {a b : G} (ha : a ∈ hF.V) (hb : b ∈ hF.V) : a * b = b * a := by
  obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn ha
  obtain ⟨q, rfl⟩ := hF.exists_vec_of_mem_V hn hb
  exact hF.vec_comm p q

def W (hn : 1 ≤ n) : Subgroup G where
  carrier := {w | w ∈ hF.V ∧ w * w = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨mul_mem ha hb, ?_⟩
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hF.V_comm hn hb ha]
      _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
  one_mem' := ⟨one_mem _, mul_one 1⟩
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    exact ⟨inv_mem ha, by rw [← mul_inv_rev, ha2, inv_one]⟩

theorem mem_W_iff (hn : 1 ≤ n) {w : G} : w ∈ hF.W hn ↔ w ∈ hF.V ∧ w * w = 1 := Iff.rfl

theorem W_le_V (hn : 1 ≤ n) : hF.W hn ≤ hF.V := fun _ hw => hw.1

theorem vec_mem_W_iff (hn : 1 ≤ n) {p : Vec n} : vec v₁ v₂ v₃ p ∈ hF.W hn ↔ p + p = 0 := by
  rw [mem_W_iff, ← hF.vec_add, hF.vec_eq_one_iff hn]
  exact ⟨fun h => h.2, fun h => ⟨hF.vec_mem_V p, h⟩⟩

theorem comm_nf_vec_iff (hn : 1 ≤ n) (q p : Vec n) (i e : ℕ) :
    vec v₁ v₂ v₃ q * s ^ i * t ^ e * vec v₁ v₂ v₃ p =
      vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q * s ^ i * t ^ e) ↔ act i e p = p := by
  have h := hF.conj_nf q p i e
  constructor
  · intro hc
    rw [mul_assoc, ← hc, inv_mul_cancel_left] at h
    exact (hF.vec_injective hn h).symm
  · intro ha
    rw [ha] at h
    calc vec v₁ v₂ v₃ q * s ^ i * t ^ e * vec v₁ v₂ v₃ p
        = (vec v₁ v₂ v₃ q * s ^ i * t ^ e) *
            ((vec v₁ v₂ v₃ q * s ^ i * t ^ e)⁻¹ * vec v₁ v₂ v₃ p *
              (vec v₁ v₂ v₃ q * s ^ i * t ^ e)) := by rw [h]
      _ = vec v₁ v₂ v₃ p * (vec v₁ v₂ v₃ q * s ^ i * t ^ e) := by group

theorem nf_trivial_of_comm (hn : 2 ≤ n) (q : Vec n) {i e : ℕ} (hi : i < 4) (he : e < 2)
    (h1 : act i e ((2 ^ (n - 1), 0, 0) : Vec n) = (2 ^ (n - 1), 0, 0))
    (h2 : act i e ((0, 2 ^ (n - 1), 0) : Vec n) = (0, 2 ^ (n - 1), 0)) : i = 0 ∧ e = 0 := by
  have hn1 : 1 ≤ n := by omega
  have hε := two_pow_pred_ne_zero hn1 (n := n)
  have hneg := neg_two_pow_pred hn1 (n := n)
  have hsub : (0 : ZMod (2 ^ n)) - 2 ^ (n - 1) = 2 ^ (n - 1) := by rw [zero_sub, hneg]
  have hε' : (0 : ZMod (2 ^ n)) ≠ 2 ^ (n - 1) := fun h => hε h.symm
  interval_cases i <;> interval_cases e
  · exact ⟨rfl, rfl⟩
  all_goals
    simp only [act_00, act_10, act_20, act_30, act_01, act_11, act_21, act_31, actS, actT,
      Prod.mk.injEq, neg_zero, add_zero, zero_add, sub_zero, hneg, hsub, sub_self, hε, hε',
      false_and, and_false] at h1 h2

theorem mem_V_of_comm (hn : 2 ≤ n) {x : G} (hx : x ∈ hF.P)
    (h1 : x * vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 0) : Vec n) =
      vec v₁ v₂ v₃ ((2 ^ (n - 1), 0, 0) : Vec n) * x)
    (h2 : x * vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) =
      vec v₁ v₂ v₃ ((0, 2 ^ (n - 1), 0) : Vec n) * x) : x ∈ hF.V := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨p, i, hi, e, he, rfl⟩ := hF.exists_nf hn1 hx
  obtain ⟨rfl, rfl⟩ := hF.nf_trivial_of_comm hn p hi he ((hF.comm_nf_vec_iff hn1 _ _ _ _).1 h1)
    ((hF.comm_nf_vec_iff hn1 _ _ _ _).1 h2)
  rw [pow_zero, pow_zero, mul_one, mul_one]
  exact hF.vec_mem_V p

theorem nf_mem_V_iff (hn : 2 ≤ n) (q : Vec n) {i e : ℕ} (hi : i < 4) (he : e < 2) :
    vec v₁ v₂ v₃ q * s ^ i * t ^ e ∈ hF.V ↔ i = 0 ∧ e = 0 := by
  have hn1 : 1 ≤ n := by omega
  constructor
  · intro hx
    refine hF.nf_trivial_of_comm hn q hi he ((hF.comm_nf_vec_iff hn1 q _ i e).1 ?_)
      ((hF.comm_nf_vec_iff hn1 q _ i e).1 ?_) <;>
      exact hF.V_comm hn1 hx (hF.vec_mem_V _)
  · rintro ⟨rfl, rfl⟩
    rw [pow_zero, pow_zero, mul_one, mul_one]
    exact hF.vec_mem_V q

theorem s_pow_mul_vec (i : ℕ) (q : Vec n) :
    s ^ i * vec v₁ v₂ v₃ q = vec v₁ v₂ v₃ (actS'^[i] q) * s ^ i := by
  induction i generalizing q with
  | zero => rw [pow_zero, one_mul, mul_one]; rfl
  | succ i ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, hF.s_mul_vec, Function.iterate_succ_apply',
      mul_assoc]

theorem sq_nf_t_mem_V (q : Vec n) (i : ℕ) : (vec v₁ v₂ v₃ q * s ^ i * t) ^ 2 ∈ hF.V := by
  have e : (vec v₁ v₂ v₃ q * s ^ i * t) ^ 2 =
      vec v₁ v₂ v₃ (q + actS'^[i] (actT q)) := by
    rw [pow_two, hF.vec_add]
    calc vec v₁ v₂ v₃ q * s ^ i * t * (vec v₁ v₂ v₃ q * s ^ i * t)
        = vec v₁ v₂ v₃ q * s ^ i * (t * vec v₁ v₂ v₃ q) * s ^ i * t := by group
      _ = vec v₁ v₂ v₃ q * (s ^ i * vec v₁ v₂ v₃ (actT q)) * (t * s ^ i) * t := by
          rw [hF.t_mul_vec]; group
      _ = vec v₁ v₂ v₃ q * vec v₁ v₂ v₃ (actS'^[i] (actT q)) := by
          rw [hF.s_pow_mul_vec, hF.t_mul_pow_s]
          simp only [mul_assoc]
          rw [hF.t_sq]
          group
  rw [e]
  exact hF.vec_mem_V _

theorem sq_nf_s (q : Vec n) (i : ℕ) :
    (vec v₁ v₂ v₃ q * s ^ i) ^ 2 = vec v₁ v₂ v₃ (q + actS'^[i] q) * s ^ (2 * i) := by
  rw [pow_two, hF.vec_add, two_mul, pow_add]
  calc vec v₁ v₂ v₃ q * s ^ i * (vec v₁ v₂ v₃ q * s ^ i)
      = vec v₁ v₂ v₃ q * (s ^ i * vec v₁ v₂ v₃ q) * s ^ i := by group
    _ = _ := by rw [hF.s_pow_mul_vec]; group

theorem pow_four_mem_V (hn : 1 ≤ n) {x : G} (hx : x ∈ hF.P) : x ^ 4 ∈ hF.V := by
  obtain ⟨q, i, -, e, he, rfl⟩ := hF.exists_nf hn hx
  have h4 : ∀ y : G, y ^ 4 = (y ^ 2) ^ 2 := fun y => by rw [← pow_mul]
  interval_cases e
  · rw [pow_zero, mul_one, h4, hF.sq_nf_s, hF.sq_nf_s, show 2 * (2 * i) = 4 * i by ring,
      pow_mul]
    exact mul_mem (hF.vec_mem_V _) (pow_mem hF.s_four_mem_V _)
  · rw [pow_one, h4]
    exact pow_mem (hF.sq_nf_t_mem_V q i) _

theorem nf_sq_mem_V_iff (hn : 2 ≤ n) (q : Vec n) {i e : ℕ} (hi : i < 4) (he : e < 2) :
    (vec v₁ v₂ v₃ q * s ^ i * t ^ e) ^ 2 ∈ hF.V ↔ e = 1 ∨ i = 0 ∨ i = 2 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨σ, hσ⟩ := hF.exists_vec_of_mem_V hn1 hF.s_four_mem_V
  interval_cases e
  · rw [pow_zero, mul_one, hF.sq_nf_s]
    interval_cases i
    · exact iff_of_true (by rw [mul_zero, pow_zero, mul_one]; exact hF.vec_mem_V _) (by omega)
    · refine iff_of_false (fun h => ?_) (by omega)
      have h' := (hF.nf_mem_V_iff hn (q + actS'^[1] q) (i := 2) (e := 0) (by norm_num)
        (by norm_num)).1 (by rwa [pow_zero, mul_one])
      omega
    · refine iff_of_true ?_ (by omega)
      rw [show 2 * 2 = 4 by rfl, ← hσ, ← hF.vec_add]
      exact hF.vec_mem_V _
    · refine iff_of_false (fun h => ?_) (by omega)
      rw [show 2 * 3 = 4 + 2 by rfl, pow_add, ← hσ, ← mul_assoc, ← hF.vec_add] at h
      have h' := (hF.nf_mem_V_iff hn (q + actS'^[3] q + σ) (i := 2) (e := 0) (by norm_num)
        (by norm_num)).1 (by rwa [pow_zero, mul_one])
      omega
  · exact iff_of_true (by rw [pow_one]; exact hF.sq_nf_t_mem_V q i) (by omega)

end AlperinFrame

end CFSG.OddStandard.ONan76
