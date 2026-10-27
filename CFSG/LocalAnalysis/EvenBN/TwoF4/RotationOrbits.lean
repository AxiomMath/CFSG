module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Finset

section Orbits

variable {n : ℕ}

@[expose] def SameTwoOrbit (x y : ZMod (2 ^ n - 1)) : Prop :=
  ∃ k : ℕ, y = 2 ^ k * x

theorem zmod_two_pow_self (n : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have h : ((2 ^ n - 1 + 1 : ℕ) : ZMod (2 ^ n - 1)) = 1 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  exact_mod_cast h

theorem zmod_two_pow_mod (n k : ℕ) : (2 : ZMod (2 ^ n - 1)) ^ (k % n) = 2 ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, zmod_two_pow_self, one_pow, mul_one]

theorem SameTwoOrbit.refl (x : ZMod (2 ^ n - 1)) : SameTwoOrbit x x :=
  ⟨0, by rw [pow_zero, one_mul]⟩

theorem SameTwoOrbit.trans {x y z : ZMod (2 ^ n - 1)} (hxy : SameTwoOrbit x y)
    (hyz : SameTwoOrbit y z) : SameTwoOrbit x z := by
  obtain ⟨k, rfl⟩ := hxy
  obtain ⟨l, rfl⟩ := hyz
  exact ⟨l + k, by rw [pow_add, mul_assoc]⟩

theorem SameTwoOrbit.symm [NeZero n] {x y : ZMod (2 ^ n - 1)} (h : SameTwoOrbit x y) :
    SameTwoOrbit y x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
  refine ⟨k * n', ?_⟩
  rw [← mul_assoc, ← pow_add, show k * n' + k = (n' + 1) * k by ring, pow_mul, zmod_two_pow_self,
    one_pow, one_mul]

theorem SameTwoOrbit.mul_left (c : ZMod (2 ^ n - 1)) {x y : ZMod (2 ^ n - 1)}
    (h : SameTwoOrbit x y) : SameTwoOrbit (c * x) (c * y) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, mul_left_comm _ _ _⟩

theorem SameTwoOrbit.neg {x y : ZMod (2 ^ n - 1)} (h : SameTwoOrbit x y) :
    SameTwoOrbit (-x) (-y) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, (mul_neg _ _).symm⟩

theorem sameTwoOrbit_zero_left {y : ZMod (2 ^ n - 1)} : SameTwoOrbit 0 y ↔ y = 0 := by
  refine ⟨?_, fun h => h ▸ SameTwoOrbit.refl 0⟩
  rintro ⟨k, rfl⟩
  exact mul_zero _

theorem sameTwoOrbit_zero_right [NeZero n] {x : ZMod (2 ^ n - 1)} : SameTwoOrbit x 0 ↔ x = 0 :=
  ⟨fun h => sameTwoOrbit_zero_left.1 h.symm, fun h => h ▸ SameTwoOrbit.refl 0⟩

theorem isUnit_two_zmod [NeZero n] : IsUnit (2 : ZMod (2 ^ n - 1)) := by
  refine isUnit_iff_exists_inv.2 ⟨2 ^ (n - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel NeZero.one_le, zmod_two_pow_self]

theorem SameTwoOrbit.isUnit_iff [NeZero n] {x y : ZMod (2 ^ n - 1)} (h : SameTwoOrbit x y) :
    IsUnit y ↔ IsUnit x := by
  obtain ⟨k, rfl⟩ := h
  rw [IsUnit.mul_iff, and_iff_right (isUnit_two_zmod.pow k)]

end Orbits

section Bits

variable {n : ℕ}

@[expose] def ofBits (S : Finset (ZMod n)) : ZMod (2 ^ n - 1) :=
  ∑ i ∈ S, 2 ^ i.val

@[expose] def rotateBits (k : ZMod n) (S : Finset (ZMod n)) : Finset (ZMod n) :=
  S.map (Equiv.addRight k).toEmbedding

theorem mem_rotateBits {k i : ZMod n} {S : Finset (ZMod n)} : i ∈ rotateBits k S ↔ i - k ∈ S := by
  simp [rotateBits, Finset.mem_map_equiv, sub_eq_add_neg]

theorem card_rotateBits (k : ZMod n) (S : Finset (ZMod n)) : (rotateBits k S).card = S.card :=
  card_map _

theorem ofBits_rotateBits [NeZero n] (k : ZMod n) (S : Finset (ZMod n)) :
    ofBits (rotateBits k S) = 2 ^ k.val * ofBits S := by
  simp only [ofBits, rotateBits, sum_map, mul_sum, ← pow_add]
  refine sum_congr rfl fun i _ => ?_
  rw [Equiv.coe_toEmbedding, Equiv.coe_addRight, ZMod.val_add, zmod_two_pow_mod, add_comm]

theorem ofBits_rotateBits_natCast [NeZero n] (k : ℕ) (S : Finset (ZMod n)) :
    ofBits (rotateBits (k : ZMod n) S) = 2 ^ k * ofBits S := by
  rw [ofBits_rotateBits, ZMod.val_natCast, zmod_two_pow_mod]

@[expose] def zmodValEmb (n : ℕ) [NeZero n] : ZMod n ↪ ℕ :=
  ⟨ZMod.val, ZMod.val_injective n⟩

theorem map_zmodValEmb_univ [NeZero n] :
    (univ : Finset (ZMod n)).map (zmodValEmb n) = range n := by
  ext j
  simp only [mem_map, mem_univ, true_and, mem_range, zmodValEmb, Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ ZMod.val_lt i, fun hj => ⟨j, ZMod.val_cast_of_lt hj⟩⟩

@[expose] def bitsNat (S : Finset (ZMod n)) : ℕ :=
  ∑ i ∈ S, 2 ^ i.val

theorem natCast_bitsNat (S : Finset (ZMod n)) : (bitsNat S : ZMod (2 ^ n - 1)) = ofBits S := by
  simp [bitsNat, ofBits]

theorem bitsNat_eq_sum_map [NeZero n] (S : Finset (ZMod n)) :
    bitsNat S = ∑ j ∈ S.map (zmodValEmb n), 2 ^ j := by
  rw [sum_map]
  rfl

theorem bitsNat_univ [NeZero n] : bitsNat (univ : Finset (ZMod n)) = 2 ^ n - 1 := by
  rw [bitsNat_eq_sum_map, map_zmodValEmb_univ, Nat.geomSum_eq le_rfl, Nat.div_one]

theorem bitsNat_injective [NeZero n] : Function.Injective (bitsNat : Finset (ZMod n) → ℕ) := by
  intro S T h
  rw [bitsNat_eq_sum_map, bitsNat_eq_sum_map] at h
  exact map_injective (zmodValEmb n) (geomSum_injective le_rfl h)

theorem bitsNat_lt [NeZero n] {S : Finset (ZMod n)} (hS : S ≠ univ) : bitsNat S < 2 ^ n - 1 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra h
    exact hS (eq_univ_iff_forall.2 fun j => by_contra fun hj => h ⟨j, hj⟩)
  rw [← bitsNat_univ]
  exact sum_lt_sum_of_subset (subset_univ S) (mem_univ j) hj (by positivity) fun _ _ _ =>
    Nat.zero_le _

theorem bitsNat_eq_zero_iff {S : Finset (ZMod n)} : bitsNat S = 0 ↔ S = ∅ := by
  simp [bitsNat, sum_eq_zero_iff, eq_empty_iff_forall_notMem]

theorem ofBits_empty : ofBits (∅ : Finset (ZMod n)) = 0 :=
  sum_empty

theorem ofBits_univ [NeZero n] : ofBits (univ : Finset (ZMod n)) = 0 := by
  rw [← natCast_bitsNat, bitsNat_univ, ZMod.natCast_self]

theorem ofBits_compl [NeZero n] (S : Finset (ZMod n)) : ofBits Sᶜ = -ofBits S := by
  refine eq_neg_of_add_eq_zero_right ?_
  rw [ofBits, ofBits, sum_add_sum_compl, ← ofBits, ofBits_univ]

theorem ofBits_eq_ofBits_iff [NeZero n] {S T : Finset (ZMod n)} :
    ofBits S = ofBits T ↔ S = T ∨ (S = ∅ ∧ T = univ) ∨ (S = univ ∧ T = ∅) := by
  constructor
  · intro h
    rw [← natCast_bitsNat, ← natCast_bitsNat, ZMod.natCast_eq_natCast_iff'] at h
    rcases eq_or_ne S univ with rfl | hS <;> rcases eq_or_ne T univ with rfl | hT
    · exact Or.inl rfl
    · rw [bitsNat_univ, Nat.mod_self, Nat.mod_eq_of_lt (bitsNat_lt hT)] at h
      exact Or.inr (Or.inr ⟨rfl, bitsNat_eq_zero_iff.1 h.symm⟩)
    · rw [bitsNat_univ, Nat.mod_self, Nat.mod_eq_of_lt (bitsNat_lt hS)] at h
      exact Or.inr (Or.inl ⟨bitsNat_eq_zero_iff.1 h, rfl⟩)
    · rw [Nat.mod_eq_of_lt (bitsNat_lt hS), Nat.mod_eq_of_lt (bitsNat_lt hT)] at h
      exact Or.inl (bitsNat_injective h)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [ofBits_empty, ofBits_univ]
    · rw [ofBits_empty, ofBits_univ]

theorem ofBits_ne_zero [NeZero n] {S : Finset (ZMod n)} (hS : S ≠ ∅) (hSu : S ≠ univ) :
    ofBits S ≠ 0 := by
  rw [← ofBits_empty, Ne, ofBits_eq_ofBits_iff]
  rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
  · exact hS h
  · exact hS h
  · exact hSu h

theorem neZero_two_pow_sub_one [NeZero n] : NeZero (2 ^ n - 1) :=
  ⟨by have := Nat.one_lt_two_pow (NeZero.ne n); omega⟩

attribute [local instance] neZero_two_pow_sub_one

end Bits

section Runs

variable {n : ℕ}

@[expose] def runStarts (S : Finset (ZMod n)) : Finset (ZMod n) :=
  S.filter fun i => i - 1 ∉ S

theorem runStarts_rotateBits (k : ZMod n) (S : Finset (ZMod n)) :
    runStarts (rotateBits k S) = rotateBits k (runStarts S) := by
  ext i
  simp only [runStarts, mem_filter, mem_rotateBits, sub_right_comm i 1 k]

theorem card_runStarts_compl [NeZero n] (S : Finset (ZMod n)) :
    (runStarts Sᶜ).card = (runStarts S).card := by
  have h1 := card_filter_add_card_filter_not (s := S) (fun i => i - 1 ∉ S)
  have h2 := card_filter_add_card_filter_not (s := S) (fun j => j + 1 ∉ S)
  have e1 : runStarts Sᶜ = rotateBits 1 (S.filter fun j => j + 1 ∉ S) := by
    ext i
    simp only [runStarts, mem_filter, mem_compl, mem_rotateBits, sub_add_cancel, not_not]
    tauto
  have e2 : (S.filter fun i => ¬ (i - 1 ∉ S)) =
      rotateBits 1 (S.filter fun j => ¬ (j + 1 ∉ S)) := by
    ext i
    simp only [mem_filter, mem_rotateBits, sub_add_cancel, not_not]
    tauto
  rw [e2, card_rotateBits] at h1
  rw [e1, card_rotateBits]
  exact Nat.add_right_cancel (h2.trans h1.symm)

end Runs

section Invariants

variable {n : ℕ} [NeZero n]

theorem not_sameTwoOrbit_ofBits {S T : Finset (ZMod n)} (hT : T ≠ ∅) (hTu : T ≠ univ)
    (h : S.card ≠ T.card ∨ (runStarts S).card ≠ (runStarts T).card) :
    ¬ SameTwoOrbit (ofBits S) (ofBits T) := by
  rintro ⟨k, hk⟩
  rw [← ofBits_rotateBits_natCast, eq_comm, ofBits_eq_ofBits_iff] at hk
  rcases hk with hk | ⟨-, hk⟩ | ⟨-, hk⟩
  · rw [← hk, card_rotateBits, runStarts_rotateBits, card_rotateBits] at h
    exact h.elim (fun h => h rfl) fun h => h rfl
  · exact hTu hk
  · exact hT hk

end Invariants

section Braces

variable (m : ℕ)

abbrev thetaExp : ZMod (2 ^ (2 * m + 1) - 1) := 2 ^ m

theorem two_mul_thetaExp_sq : 2 * thetaExp m ^ 2 = 1 := by
  rw [thetaExp, ← pow_mul, ← pow_succ', show m * 2 + 1 = 2 * m + 1 by ring, zmod_two_pow_self]

@[expose] def runBits : Finset (ZMod (2 * m + 1)) :=
  (range m).image fun j : ℕ => ((j + 1 : ℕ) : ZMod (2 * m + 1))

@[expose] def pairBits : Finset (ZMod (2 * m + 1)) :=
  {1, ((m + 1 : ℕ) : ZMod (2 * m + 1))}

variable {m}

theorem val_one_zmod_two_mul_add_one (hm : 1 ≤ m) : (1 : ZMod (2 * m + 1)).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]

theorem natCast_succ_injOn_range :
    Set.InjOn (fun j : ℕ => ((j + 1 : ℕ) : ZMod (2 * m + 1))) (range m : Set ℕ) := by
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  have h := congrArg ZMod.val hab
  simp only at h
  rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega), Nat.add_right_cancel_iff]
    at h

theorem mem_runBits {i : ZMod (2 * m + 1)} :
    i ∈ runBits m ↔ ∃ j < m, ((j + 1 : ℕ) : ZMod (2 * m + 1)) = i := by
  simp [runBits]

theorem one_ne_natCast_succ_zmod (hm : 1 ≤ m) :
    (1 : ZMod (2 * m + 1)) ≠ ((m + 1 : ℕ) : ZMod (2 * m + 1)) := by
  intro h
  have h' := congrArg ZMod.val h
  rw [val_one_zmod_two_mul_add_one hm, ZMod.val_cast_of_lt (by omega)] at h'
  omega

theorem ofBits_singleton_one (hm : 1 ≤ m) : ofBits ({1} : Finset (ZMod (2 * m + 1))) = 2 := by
  rw [ofBits, sum_singleton, val_one_zmod_two_mul_add_one hm, pow_one]

theorem ofBits_runBits : ofBits (runBits m) = 2 * thetaExp m - 2 := by
  rw [ofBits, runBits, sum_image natCast_succ_injOn_range]
  have h : ∀ j ∈ range m,
      (2 : ZMod (2 ^ (2 * m + 1) - 1)) ^ ((j + 1 : ℕ) : ZMod (2 * m + 1)).val = 2 * 2 ^ j := by
    intro j hj
    rw [mem_range] at hj
    rw [ZMod.val_cast_of_lt (by omega), pow_succ' (2 : ZMod (2 ^ (2 * m + 1) - 1)) j]
  rw [sum_congr rfl h, ← mul_sum]
  have hg := geom_sum_mul (2 : ZMod (2 ^ (2 * m + 1) - 1)) m
  rw [show (2 : ZMod (2 ^ (2 * m + 1) - 1)) - 1 = 1 by ring, mul_one] at hg
  rw [hg, thetaExp]
  ring

theorem ofBits_pairBits (hm : 1 ≤ m) : ofBits (pairBits m) = 2 * thetaExp m + 2 := by
  rw [ofBits, pairBits, sum_pair (one_ne_natCast_succ_zmod hm), val_one_zmod_two_mul_add_one hm,
    ZMod.val_cast_of_lt (by omega), thetaExp]
  ring

theorem card_runBits : (runBits m).card = m := by
  rw [runBits, card_image_of_injOn natCast_succ_injOn_range, card_range]

theorem card_pairBits (hm : 1 ≤ m) : (pairBits m).card = 2 :=
  card_pair (one_ne_natCast_succ_zmod hm)

theorem card_compl_bits (S : Finset (ZMod (2 * m + 1))) : Sᶜ.card = 2 * m + 1 - S.card := by
  rw [card_compl, ZMod.card]

theorem runStarts_runBits (hm : 1 ≤ m) : runStarts (runBits m) = {1} := by
  ext i
  simp only [runStarts, mem_filter, mem_singleton, mem_runBits]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hnot⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · refine absurd ⟨j - 1, by omega, ?_⟩ hnot
      rw [Nat.sub_add_cancel hj0]
      push_cast
      ring
  · rintro rfl
    refine ⟨⟨0, hm, by simp⟩, ?_⟩
    rintro ⟨j, hj, hj'⟩
    have h := congrArg ZMod.val hj'
    rw [sub_self, ZMod.val_zero, ZMod.val_cast_of_lt (by omega)] at h
    omega

theorem runStarts_pairBits (hm : 2 ≤ m) : runStarts (pairBits m) = pairBits m := by
  refine filter_true_of_mem fun i hi => ?_
  have hv1 := val_one_zmod_two_mul_add_one (m := m) (by omega)
  have hvm : ∀ j < 2 * m + 1, ((j : ℕ) : ZMod (2 * m + 1)).val = j :=
    fun j hj => ZMod.val_cast_of_lt hj
  have hsub : ((m + 1 : ℕ) : ZMod (2 * m + 1)) - 1 = ((m : ℕ) : ZMod (2 * m + 1)) := by
    push_cast
    ring
  simp only [pairBits, mem_insert, mem_singleton] at hi ⊢
  rintro (h | h) <;> rcases hi with rfl | rfl
  · have h' := congrArg ZMod.val h
    rw [sub_self, ZMod.val_zero, hv1] at h'
    omega
  · have h' := congrArg ZMod.val h
    rw [hsub, hvm m (by omega), hv1] at h'
    omega
  · have h' := congrArg ZMod.val h
    rw [sub_self, ZMod.val_zero, hvm (m + 1) (by omega)] at h'
    omega
  · have h' := congrArg ZMod.val h
    rw [hsub, hvm m (by omega), hvm (m + 1) (by omega)] at h'
    omega

theorem not_sameTwoOrbit_brace_bits (hm : 1 ≤ m) {S T : Finset (ZMod (2 * m + 1))}
    (hS : S = {1} ∨ S = runBits m ∨ S = (pairBits m)ᶜ)
    (hT : T = {1}ᶜ ∨ T = (runBits m)ᶜ ∨ T = pairBits m) :
    ¬ SameTwoOrbit (ofBits S) (ofBits T) := by
  have c1 : ({1} : Finset (ZMod (2 * m + 1))).card = 1 := card_singleton 1
  have c2 := card_runBits (m := m)
  have c3 := card_pairBits hm
  have r2 : (runStarts (runBits m)).card = 1 := by rw [runStarts_runBits hm, card_singleton]
  have hT0 : 0 < T.card ∧ T.card < 2 * m + 1 := by
    rcases hT with rfl | rfl | rfl <;> simp only [card_compl_bits, c1, c2, c3] <;> omega
  have hTe : T ≠ ∅ := by
    rintro rfl
    simp at hT0
  have hTu : T ≠ univ := by
    rintro rfl
    rw [card_univ, ZMod.card] at hT0
    omega
  refine not_sameTwoOrbit_ofBits hTe hTu ?_
  rcases eq_or_ne m 2 with rfl | hm2
  · have r3 : (runStarts (pairBits 2)).card = 2 := by rw [runStarts_pairBits le_rfl, c3]
    rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl <;>
      simp only [card_compl_bits, card_runStarts_compl, c1, c2, c3, r2, r3] <;> omega
  · rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl <;>
      simp only [card_compl_bits, c1, c2, c3] <;> omega

end Braces

section BraceClasses

variable (m : ℕ)

@[expose] def IsBraceTwo (x : ZMod (2 ^ (2 * m + 1) - 1)) : Prop :=
  SameTwoOrbit 2 x ∨ SameTwoOrbit (2 * thetaExp m - 2) x ∨ SameTwoOrbit (-2 * thetaExp m - 2) x

@[expose] def IsBraceNegTwo (x : ZMod (2 ^ (2 * m + 1) - 1)) : Prop :=
  IsBraceTwo m (-x)

@[expose] def DifferentBraces (x y : ZMod (2 ^ (2 * m + 1) - 1)) : Prop :=
  (x = 0 ∧ y ≠ 0) ∨ (x ≠ 0 ∧ y = 0) ∨ (IsBraceTwo m x ∧ IsBraceNegTwo m y) ∨
    (IsBraceNegTwo m x ∧ IsBraceTwo m y)

variable {m}

theorem isBraceNegTwo_neg_iff {x : ZMod (2 ^ (2 * m + 1) - 1)} :
    IsBraceNegTwo m (-x) ↔ IsBraceTwo m x := by
  rw [IsBraceNegTwo, neg_neg]

theorem IsBraceTwo.exists_bits (hm : 1 ≤ m) {x : ZMod (2 ^ (2 * m + 1) - 1)}
    (hx : IsBraceTwo m x) :
    ∃ S : Finset (ZMod (2 * m + 1)), (S = {1} ∨ S = runBits m ∨ S = (pairBits m)ᶜ) ∧
      SameTwoOrbit (ofBits S) x := by
  rcases hx with h | h | h
  · exact ⟨{1}, Or.inl rfl, by rwa [ofBits_singleton_one hm]⟩
  · exact ⟨runBits m, Or.inr (Or.inl rfl), by rwa [ofBits_runBits]⟩
  · refine ⟨(pairBits m)ᶜ, Or.inr (Or.inr rfl), ?_⟩
    rwa [ofBits_compl, ofBits_pairBits hm,
      show -(2 * thetaExp m + 2) = -2 * thetaExp m - 2 by ring]

theorem IsBraceNegTwo.exists_bits (hm : 1 ≤ m) {x : ZMod (2 ^ (2 * m + 1) - 1)}
    (hx : IsBraceNegTwo m x) :
    ∃ T : Finset (ZMod (2 * m + 1)), (T = {1}ᶜ ∨ T = (runBits m)ᶜ ∨ T = pairBits m) ∧
      SameTwoOrbit (ofBits T) x := by
  obtain ⟨S, hS, h⟩ := IsBraceTwo.exists_bits hm hx
  have h' := h.neg
  rw [neg_neg, ← ofBits_compl] at h'
  refine ⟨Sᶜ, ?_, h'⟩
  rcases hS with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (compl_compl _))

theorem IsBraceTwo.not_sameTwoOrbit (hm : 1 ≤ m) {x y : ZMod (2 ^ (2 * m + 1) - 1)}
    (hx : IsBraceTwo m x) (hy : IsBraceNegTwo m y) : ¬ SameTwoOrbit x y := by
  intro hxy
  obtain ⟨S, hS, hSx⟩ := hx.exists_bits hm
  obtain ⟨T, hT, hTy⟩ := hy.exists_bits hm
  exact not_sameTwoOrbit_brace_bits hm hS hT (hSx.trans (hxy.trans hTy.symm))

theorem IsBraceNegTwo.not_sameTwoOrbit (hm : 1 ≤ m) {x y : ZMod (2 ^ (2 * m + 1) - 1)}
    (hx : IsBraceNegTwo m x) (hy : IsBraceTwo m y) : ¬ SameTwoOrbit x y :=
  fun h => hy.not_sameTwoOrbit hm hx h.symm

theorem IsBraceTwo.ne_zero (hm : 1 ≤ m) {x : ZMod (2 ^ (2 * m + 1) - 1)} (hx : IsBraceTwo m x) :
    x ≠ 0 := by
  rintro rfl
  obtain ⟨S, hS, h⟩ := hx.exists_bits hm
  refine ofBits_ne_zero (S := S) ?_ ?_ (sameTwoOrbit_zero_right.1 h)
  · rcases hS with rfl | rfl | rfl
    · exact singleton_ne_empty 1
    · intro h
      have h' := card_runBits (m := m)
      rw [h, card_empty] at h'
      omega
    · rw [Ne, ← card_eq_zero, card_compl_bits, card_pairBits hm]
      omega
  · rcases hS with rfl | rfl | rfl
    · rw [Ne, ← card_eq_iff_eq_univ, card_singleton, ZMod.card]
      omega
    · rw [Ne, ← card_eq_iff_eq_univ, card_runBits, ZMod.card]
      omega
    · rw [Ne, ← card_eq_iff_eq_univ, card_compl_bits, card_pairBits hm, ZMod.card]
      omega

theorem IsBraceNegTwo.ne_zero (hm : 1 ≤ m) {x : ZMod (2 ^ (2 * m + 1) - 1)}
    (hx : IsBraceNegTwo m x) : x ≠ 0 :=
  fun h => IsBraceTwo.ne_zero hm hx (by rw [h, neg_zero])

theorem DifferentBraces.not_sameTwoOrbit (hm : 1 ≤ m) {x y : ZMod (2 ^ (2 * m + 1) - 1)}
    (h : DifferentBraces m x y) : ¬ SameTwoOrbit x y := by
  rcases h with ⟨rfl, hy⟩ | ⟨hx, rfl⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact fun h => hy (sameTwoOrbit_zero_left.1 h)
  · exact fun h => hx (sameTwoOrbit_zero_right.1 h)
  · exact hx.not_sameTwoOrbit hm hy
  · exact hx.not_sameTwoOrbit hm hy

theorem isBraceTwo_two : IsBraceTwo m 2 :=
  Or.inl (SameTwoOrbit.refl _)

theorem isBraceTwo_two_mul_thetaExp : IsBraceTwo m (2 * thetaExp m) :=
  Or.inl ⟨m, mul_comm _ _⟩

theorem isBraceTwo_four_mul_thetaExp : IsBraceTwo m (4 * thetaExp m) :=
  Or.inl ⟨m + 1, by rw [thetaExp, pow_succ (2 : ZMod (2 ^ (2 * m + 1) - 1)) m]; ring⟩

theorem isBraceTwo_two_mul_thetaExp_sub_two : IsBraceTwo m (2 * thetaExp m - 2) :=
  Or.inr (Or.inl (SameTwoOrbit.refl _))

theorem isBraceTwo_neg_four_mul_thetaExp_add_two : IsBraceTwo m (-4 * thetaExp m + 2) := by
  refine Or.inr (Or.inl ⟨m + 1, ?_⟩)
  have h := two_mul_thetaExp_sq m
  rw [pow_succ (2 : ZMod (2 ^ (2 * m + 1) - 1)) m]
  rw [thetaExp] at h ⊢
  linear_combination (-2 : ZMod (2 ^ (2 * m + 1) - 1)) * h

theorem isBraceTwo_neg_two_mul_thetaExp_sub_two : IsBraceTwo m (-2 * thetaExp m - 2) :=
  Or.inr (Or.inr (SameTwoOrbit.refl _))

theorem isBraceNegTwo_neg_two : IsBraceNegTwo m (-2) :=
  isBraceNegTwo_neg_iff.2 isBraceTwo_two

theorem isBraceNegTwo_neg_two_mul_thetaExp : IsBraceNegTwo m (-2 * thetaExp m) := by
  rw [IsBraceNegTwo, show -(-2 * thetaExp m) = 2 * thetaExp m by ring]
  exact isBraceTwo_two_mul_thetaExp

theorem isBraceNegTwo_neg_four_mul_thetaExp : IsBraceNegTwo m (-4 * thetaExp m) := by
  rw [IsBraceNegTwo, show -(-4 * thetaExp m) = 4 * thetaExp m by ring]
  exact isBraceTwo_four_mul_thetaExp

theorem isBraceNegTwo_neg_two_mul_thetaExp_add_two :
    IsBraceNegTwo m (-2 * thetaExp m + 2) := by
  rw [IsBraceNegTwo, show -(-2 * thetaExp m + 2) = 2 * thetaExp m - 2 by ring]
  exact isBraceTwo_two_mul_thetaExp_sub_two

theorem isBraceNegTwo_two_mul_thetaExp_add_two : IsBraceNegTwo m (2 * thetaExp m + 2) := by
  rw [IsBraceNegTwo, show -(2 * thetaExp m + 2) = -2 * thetaExp m - 2 by ring]
  exact isBraceTwo_neg_two_mul_thetaExp_sub_two

theorem isUnit_thetaExp_sub_one : IsUnit (thetaExp m - 1) := by
  refine isUnit_iff_exists_inv.2 ⟨-2 * (thetaExp m + 1), ?_⟩
  linear_combination (-1 : ZMod (2 ^ (2 * m + 1) - 1)) * two_mul_thetaExp_sq m

theorem isUnit_thetaExp_add_one : IsUnit (thetaExp m + 1) := by
  refine isUnit_iff_exists_inv.2 ⟨-2 * (thetaExp m - 1), ?_⟩
  linear_combination (-1 : ZMod (2 ^ (2 * m + 1) - 1)) * two_mul_thetaExp_sq m

theorem IsBraceTwo.isUnit {x : ZMod (2 ^ (2 * m + 1) - 1)} (hx : IsBraceTwo m x) : IsUnit x := by
  rcases hx with h | h | h
  · exact h.isUnit_iff.2 isUnit_two_zmod
  · refine h.isUnit_iff.2 ?_
    rw [show 2 * thetaExp m - 2 = 2 * (thetaExp m - 1) by ring]
    exact isUnit_two_zmod.mul isUnit_thetaExp_sub_one
  · refine h.isUnit_iff.2 ?_
    rw [show -2 * thetaExp m - 2 = -(2 * (thetaExp m + 1)) by ring]
    exact (isUnit_two_zmod.mul isUnit_thetaExp_add_one).neg

theorem IsBraceNegTwo.isUnit {x : ZMod (2 ^ (2 * m + 1) - 1)} (hx : IsBraceNegTwo m x) :
    IsUnit x :=
  (IsUnit.neg_iff x).1 (IsBraceTwo.isUnit hx)

end BraceClasses

end CFSG.LocalAnalysis.EvenBN.TwoF4
