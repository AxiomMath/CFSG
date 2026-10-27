module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Finset

theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {l : ℕ} (hx : x ^ l = 1)
    (n : ℕ) : x ^ n = x ^ (n % l) := by
  conv_lhs => rw [← Nat.div_add_mod n l, pow_add, pow_mul, hx, one_pow, one_mul]

theorem sum_range_mul_mod {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l i : ℕ}
    (hcop : Nat.Coprime l i) :
    ∑ j ∈ range l, f (j * i % l) = ∑ k ∈ range l, f k := by
  classical
  have hinj : Set.InjOn (fun j => j * i % l) (range l : Set ℕ) := by
    intro j₁ h₁ j₂ h₂ h
    simp only [coe_range, Set.mem_Iio] at h₁ h₂
    have h' : j₁ * i ≡ j₂ * i [MOD l] := h
    have h'' := Nat.ModEq.cancel_right_of_coprime hcop h'
    rwa [Nat.ModEq, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h''
  have himage : (range l).image (fun j => j * i % l) = range l := by
    apply eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      have hl : 0 < l := by
        rcases Nat.eq_zero_or_pos l with h0 | h0
        · simp [h0] at hj
        · exact h0
      exact mem_range.mpr (Nat.mod_lt _ hl)
    · rw [card_image_of_injOn hinj]
  calc ∑ j ∈ range l, f (j * i % l) = ∑ k ∈ (range l).image (fun j => j * i % l), f k :=
        (sum_image hinj).symm
    _ = ∑ k ∈ range l, f k := by rw [himage]

theorem sum_range_pow_mul {R : Type*} [Semiring R] {a : R} {l : ℕ} (hl : l.Prime)
    (ha : a ^ l = 1) {i : ℕ} (hi0 : 0 < i) (hil : i < l) :
    ∑ j ∈ range l, a ^ (j * i) = ∑ k ∈ range l, a ^ k := by
  have hcop : Nat.Coprime l i :=
    (Nat.Prime.coprime_iff_not_dvd hl).mpr (Nat.not_dvd_of_pos_of_lt hi0 hil)
  have h := sum_range_mul_mod (fun k => a ^ k) hcop
  rw [← h]
  exact sum_congr rfl fun j _ => pow_eq_pow_mod_of_pow_eq_one ha _

theorem mul_geom_sum_eq_of_pow_eq_one {R : Type*} [Ring R] {x : R} {n : ℕ} (hx : x ^ n = 1) :
    x * ∑ i ∈ range n, x ^ i = ∑ i ∈ range n, x ^ i := by
  have h := mul_geom_sum x n
  rw [hx, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem sum_geom_sum_mul_pow {R : Type*} [Ring R] {a b : R} (hab : Commute a b) {l : ℕ}
    (hl : l.Prime) (ha : a ^ l = 1) :
    ∑ j ∈ range l, ∑ i ∈ range l, (b * a ^ j) ^ i =
      (l : R) + (∑ i ∈ range l, b ^ i - 1) * ∑ i ∈ range l, a ^ i := by
  have h1 : ∀ j i, (b * a ^ j) ^ i = b ^ i * a ^ (j * i) := by
    intro j i
    rw [(hab.symm.pow_right j).mul_pow, ← pow_mul]
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have hsplit : ∀ f : ℕ → R, ∑ i ∈ range l, f i = f 0 + ∑ i ∈ Ico 1 l, f i := by
    intro f
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hl.pos]
  rw [hsplit (fun i => b ^ i * ∑ j ∈ range l, a ^ (j * i)), hsplit (fun i => b ^ i)]
  have h2 : ∑ i ∈ Ico 1 l, b ^ i * ∑ j ∈ range l, a ^ (j * i) =
      ∑ i ∈ Ico 1 l, b ^ i * ∑ k ∈ range l, a ^ k := by
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hil⟩ := mem_Ico.mp hi
    rw [sum_range_pow_mul hl ha hi1 hil]
  rw [h2, ← sum_mul]
  simp only [pow_zero, mul_zero, one_mul, sum_const, card_range, nsmul_eq_mul, mul_one,
    add_sub_cancel_left]

theorem natCast_eq_one_of_odd {R : Type*} [Ring R] (h2 : (2 : R) = 0) {n : ℕ} (hn : Odd n) :
    (n : R) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  push_cast
  rw [h2, zero_mul, zero_add]

theorem eq_one_of_geom_sum_eq_zero {R : Type*} [Ring R] (h2 : (2 : R) = 0) {a b : R}
    (hab : Commute a b) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (ha : a ^ l = 1)
    (h : ∀ j < l, ∑ i ∈ range l, (b * a ^ j) ^ i = 0) : a = 1 := by
  have hid := sum_geom_sum_mul_pow hab hl ha
  have hzero : ∑ j ∈ range l, ∑ i ∈ range l, (b * a ^ j) ^ i = 0 :=
    sum_eq_zero fun j hj => h j (mem_range.mp hj)
  have hb0 : ∑ i ∈ range l, b ^ i = 0 := by simpa using h 0 hl.pos
  rw [hzero, hb0, natCast_eq_one_of_odd h2 (hl.odd_of_ne_two hl2), zero_sub, neg_one_mul]
    at hid
  have hS : ∑ i ∈ range l, a ^ i = 1 := (add_neg_eq_zero.mp hid.symm).symm
  calc a = a * ∑ i ∈ range l, a ^ i := by rw [hS, mul_one]
    _ = ∑ i ∈ range l, a ^ i := mul_geom_sum_eq_of_pow_eq_one ha
    _ = 1 := hS

section Section

variable {V : Type*} [AddCommGroup V]

theorem odd_nsmul_eq (hV : ∀ v : V, v + v = 0) {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_comm, mul_nsmul, two_nsmul, hV]
  simp

theorem two_eq_zero_end (hV : ∀ v : V, v + v = 0) : (2 : AddMonoid.End V) = 0 := by
  ext v
  rw [AddMonoid.End.ofNat_apply, two_nsmul, hV]
  rfl

theorem pow_apply_mem {f : AddMonoid.End V} {W : AddSubgroup V} (hf : ∀ w ∈ W, f w ∈ W)
    (n : ℕ) : ∀ w ∈ W, (f ^ n) w ∈ W := by
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih =>
    intro w hw
    rw [pow_succ]
    exact ih _ (hf w hw)

theorem sum_apply_mem {ι : Type*} (s : Finset ι) {f : ι → AddMonoid.End V}
    {W W' : AddSubgroup V} (hf : ∀ i ∈ s, ∀ w ∈ W, f i w ∈ W') :
    ∀ w ∈ W, (∑ i ∈ s, f i) w ∈ W' := by
  classical
  intro w hw
  induction s using Finset.induction_on with
  | empty => exact W'.zero_mem
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact W'.add_mem (hf i (mem_insert_self _ _) w hw)
      (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem geom_sum_apply_mem_of_free {g : AddMonoid.End V} {n : ℕ} (hg : g ^ n = 1)
    {W₁ W₂ : AddSubgroup V} (hg₂ : ∀ w ∈ W₂, g w ∈ W₂)
    (hfree : ∀ w ∈ W₂, g w - w ∈ W₁ → w ∈ W₁) :
    ∀ w ∈ W₂, (∑ i ∈ range n, g ^ i) w ∈ W₁ := by
  intro w hw
  apply hfree _ (sum_apply_mem _ (fun i _ => pow_apply_mem hg₂ i) w hw)
  have e : g ((∑ i ∈ range n, g ^ i) w) = (∑ i ∈ range n, g ^ i) w := by
    change (g * ∑ i ∈ range n, g ^ i) w = _
    rw [mul_geom_sum_eq_of_pow_eq_one hg]
  rw [e, sub_self]
  exact W₁.zero_mem

theorem sub_mem_of_free (hV : ∀ v : V, v + v = 0) {a b : AddMonoid.End V} (hab : Commute a b)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (ha : a ^ l = 1) (hb : b ^ l = 1)
    {W₁ W₂ : AddSubgroup V} (ha₁ : ∀ w ∈ W₁, a w ∈ W₁) (ha₂ : ∀ w ∈ W₂, a w ∈ W₂)
    (hb₂ : ∀ w ∈ W₂, b w ∈ W₂)
    (hfree : ∀ j < l, ∀ w ∈ W₂, (b * a ^ j) w - w ∈ W₁ → w ∈ W₁) :
    ∀ w ∈ W₂, a w - w ∈ W₁ := by
  intro w hw
  have hpow : ∀ j, (b * a ^ j) ^ l = 1 := fun j => by
    rw [(hab.symm.pow_right j).mul_pow, hb, ← pow_mul, mul_comm, pow_mul, ha, one_pow, one_mul]
  have hmem2 : ∀ j, ∀ w ∈ W₂, (b * a ^ j) w ∈ W₂ :=
    fun j w hw => hb₂ _ (pow_apply_mem ha₂ j w hw)
  have hid := congrArg (fun f : AddMonoid.End V => f w) (sum_geom_sum_mul_pow hab hl ha)
  have hL : (∑ j ∈ range l, ∑ i ∈ range l, (b * a ^ j) ^ i) w ∈ W₁ := by
    refine sum_apply_mem _ (fun j hj => ?_) w hw
    exact geom_sum_apply_mem_of_free (hpow j) (hmem2 j) (hfree j (mem_range.mp hj))
  rw [hid] at hL
  have hSa2 : (∑ i ∈ range l, a ^ i) w ∈ W₂ :=
    sum_apply_mem _ (fun i _ => pow_apply_mem ha₂ i) w hw
  have hbfree : ∀ w ∈ W₂, b w - w ∈ W₁ → w ∈ W₁ := by simpa using hfree 0 hl.pos
  have hSb : (∑ i ∈ range l, b ^ i) ((∑ i ∈ range l, a ^ i) w) ∈ W₁ :=
    geom_sum_apply_mem_of_free hb hb₂ hbfree _ hSa2
  have e1 : ((l : AddMonoid.End V) + (∑ i ∈ range l, b ^ i - 1) * ∑ i ∈ range l, a ^ i) w =
      l • w + ((∑ i ∈ range l, b ^ i) ((∑ i ∈ range l, a ^ i) w) -
        (∑ i ∈ range l, a ^ i) w) := rfl
  rw [e1, odd_nsmul_eq hV (hl.odd_of_ne_two hl2)] at hL
  have hw1 : w - (∑ i ∈ range l, a ^ i) w ∈ W₁ := by
    have h3 := W₁.sub_mem hL hSb
    have e2 : w + ((∑ i ∈ range l, b ^ i) ((∑ i ∈ range l, a ^ i) w) -
        (∑ i ∈ range l, a ^ i) w) - (∑ i ∈ range l, b ^ i) ((∑ i ∈ range l, a ^ i) w) =
        w - (∑ i ∈ range l, a ^ i) w := by abel
    rwa [e2] at h3
  have hfix : a ((∑ i ∈ range l, a ^ i) w) = (∑ i ∈ range l, a ^ i) w := by
    change (a * ∑ i ∈ range l, a ^ i) w = _
    rw [mul_geom_sum_eq_of_pow_eq_one ha]
  have e3 : a w - w = a (w - (∑ i ∈ range l, a ^ i) w) - (w - (∑ i ∈ range l, a ^ i) w) := by
    rw [map_sub, hfix]
    abel
  rw [e3]
  exact W₁.sub_mem (ha₁ _ hw1) hw1

end Section

end SixNineCount

end CFSG.SeitzReduction.RankOne
