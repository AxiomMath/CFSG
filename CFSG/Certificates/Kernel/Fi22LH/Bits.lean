module

public import CFSG.Certificates.Kernel.Fi22LH.Defs
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native

@[expose] def BitsIs (B : Bits) (S : Nat → Prop) : Prop :=
  B.size = 55 ∧ ∀ y < 3520, bitAt B y = true ↔ S y

theorem bne_toNat (a : UInt64) : (a != 0) = (a.toNat != 0) := by
  rcases Decidable.em (a = 0) with h | h
  · subst h
    rfl
  · have h' : a.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [bne_iff_ne.2 h, bne_iff_ne.2 h']

theorem bitAt_eq (B : Bits) (x : Nat) : bitAt B x = (B[x / 64]!).toNat.testBit (x % 64) := by
  unfold bitAt
  generalize B[x / 64]! = w
  have hi : (UInt64.ofNat (x % 64)).toNat % 64 = x % 64 := by
    rw [UInt64.toNat_ofNat']
    omega
  have h1 : ((w >>> UInt64.ofNat (x % 64)) &&& 1).toNat = 1 &&& w.toNat >>> (x % 64) := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hi, Nat.and_comm]
    rfl
  rw [bne_toNat, h1]
  rfl

theorem testBit_toNat_ge (w : UInt64) {i : Nat} (hi : 64 ≤ i) : w.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt64.toNat_lt w)
    (Nat.pow_le_pow_right (by omega) hi))

theorem bits_ext {B C : Bits} (hB : B.size = 55) (hC : C.size = 55)
    (h : ∀ x < 3520, bitAt B x = bitAt C x) : B = C := by
  apply Array.ext (hB.trans hC.symm)
  intro w h1 h2
  have hw : w < 55 := hB ▸ h1
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have := h (64 * w + i) (by omega)
    rw [bitAt_eq, bitAt_eq] at this
    have e1 : (64 * w + i) / 64 = w := by omega
    have e2 : (64 * w + i) % 64 = i := by omega
    rw [e1, e2, getElem!_pos B w h1, getElem!_pos C w h2] at this
    exact this
  · rw [testBit_toNat_ge _ (by omega), testBit_toNat_ge _ (by omega)]

theorem BitsIs.eq {B C : Bits} {S S' : Nat → Prop} (hB : BitsIs B S) (hC : BitsIs C S')
    (h : ∀ y < 3520, S y ↔ S' y) : B = C := by
  refine bits_ext hB.1 hC.1 fun x hx => ?_
  apply Bool.eq_iff_iff.2
  rw [hB.2 x hx, hC.2 x hx]
  exact h x hx

theorem BitsIs.congr {B : Bits} {S S' : Nat → Prop} (hB : BitsIs B S)
    (h : ∀ y < 3520, S y ↔ S' y) : BitsIs B S' :=
  ⟨hB.1, fun y hy => (hB.2 y hy).trans (h y hy)⟩

theorem bitsIs_bitsOfNat (n : Nat) : BitsIs (bitsOfNat n) fun y => n.testBit y = true := by
  refine ⟨by simp [bitsOfNat], fun y hy => ?_⟩
  rw [bitAt_eq]
  have hw : y / 64 < 55 := by omega
  unfold bitsOfNat
  rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_ofFn, UInt64.toNat_ofNat',
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have e : 64 * (y / 64) + y % 64 = y := by omega
  simp only [Nat.mod_lt _ (by omega : 0 < 64), decide_true, Bool.true_and, e]

theorem bitsOfNat_inj {a b : Nat} (ha : a < 2 ^ 3520) (hb : b < 2 ^ 3520)
    (h : bitsOfNat a = bitsOfNat b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 3520
  · have h1 := (bitsIs_bitsOfNat a).2 i hi
    have h2 := (bitsIs_bitsOfNat b).2 i hi
    rw [h] at h1
    exact Bool.eq_iff_iff.2 (h1.symm.trans h2)
  · have hp : 2 ^ 3520 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem BitsIs.eq_bitsOfNat {B : Bits} {S : Nat → Prop} (hB : BitsIs B S) {n : Nat}
    (h : ∀ y < 3520, S y ↔ n.testBit y = true) : B = bitsOfNat n :=
  hB.eq (bitsIs_bitsOfNat n) h

theorem bitsIs_empty : BitsIs (emptyBits ()) fun _ => False := by
  refine ⟨by simp [emptyBits], fun y hy => ?_⟩
  rw [bitAt_eq]
  unfold emptyBits
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_replicate]
  simp

theorem bitsIs_setBit {B : Bits} {S : Nat → Prop} (hB : BitsIs B S) {x : Nat} (hx : x < 3520) :
    BitsIs (setBit B x) fun y => S y ∨ y = x := by
  have hs : (setBit B x).size = 55 := by
    unfold setBit
    rw [Array.size_modify, hB.1]
  refine ⟨hs, fun y hy => ?_⟩
  dsimp only
  rw [← hB.2 y hy, bitAt_eq, bitAt_eq]
  have hw : y / 64 < B.size := by rw [hB.1]; omega
  unfold setBit
  rw [getElem!_pos (B.modify (x / 64) fun w => w ||| (1 : UInt64) <<< UInt64.ofNat (x % 64))
    (y / 64) (by rw [Array.size_modify]; exact hw), Array.getElem_modify, getElem!_pos B _ hw]
  by_cases e : x / 64 = y / 64
  · rw [if_pos e, UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_shiftLeft]
    have h1 : ((1 : UInt64).toNat <<< ((UInt64.ofNat (x % 64)).toNat % 64)) % 2 ^ 64 =
        2 ^ (x % 64) := by
      rw [UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl, Nat.one_shiftLeft]
      have : x % 64 % 2 ^ 64 % 64 = x % 64 := by omega
      rw [this]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    rw [h1, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by omega)
  · rw [if_neg e]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact absurd (by rw [h]) e

theorem bitsIs_foldl_setBit : ∀ (l : List Nat) {B : Bits} {S : Nat → Prop}, BitsIs B S →
    (∀ a ∈ l, a < 3520) → BitsIs (l.foldl setBit B) fun y => S y ∨ y ∈ l
  | [], B, S, hB, _ => hB.congr fun y _ => by simp
  | a :: l, B, S, hB, hl => by
    rw [List.foldl_cons]
    refine (bitsIs_foldl_setBit l (bitsIs_setBit hB (hl a List.mem_cons_self))
      fun b hb => hl b (List.mem_cons_of_mem a hb)).congr fun y _ => ?_
    simp only [List.mem_cons]
    exact or_assoc

theorem bitsIs_bitsOf {xs : Array Nat} (hx : ∀ a ∈ xs, a < 3520) :
    BitsIs (bitsOf xs) fun y => y ∈ xs := by
  unfold bitsOf
  rw [← Array.foldl_toList]
  refine (bitsIs_foldl_setBit xs.toList bitsIs_empty fun a ha => hx a (Array.mem_toList_iff.1 ha)).congr
    fun y _ => ?_
  simp

theorem bitsIs_andBits {A B : Bits} {S S' : Nat → Prop} (hA : BitsIs A S) (hB : BitsIs B S') :
    BitsIs (andBits A B) fun y => S y ∧ S' y := by
  refine ⟨by simp [andBits], fun y hy => ?_⟩
  dsimp only
  rw [← hA.2 y hy, ← hB.2 y hy, bitAt_eq, bitAt_eq, bitAt_eq]
  have hw : y / 64 < 55 := by omega
  unfold andBits
  rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_ofFn, UInt64.toNat_and,
    Nat.testBit_and, Bool.and_eq_true]

theorem bitsIs_diffBits {A B : Bits} {S S' : Nat → Prop} (hA : BitsIs A S) (hB : BitsIs B S') :
    BitsIs (diffBits A B) fun y => S y ∧ ¬ S' y := by
  refine ⟨by simp [diffBits], fun y hy => ?_⟩
  dsimp only
  rw [← hA.2 y hy, ← hB.2 y hy, bitAt_eq, bitAt_eq, bitAt_eq]
  have hw : y / 64 < 55 := by omega
  unfold diffBits
  rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_ofFn, UInt64.toNat_and,
    Nat.testBit_and, Bool.and_eq_true, UInt64.toNat_not]
  have e : UInt64.size - 1 - (B[y / 64]!).toNat = 2 ^ 64 - ((B[y / 64]!).toNat + 1) := by
    have := UInt64.toNat_lt (B[y / 64]!)
    change 2 ^ 64 - 1 - _ = _
    omega
  simp only [e, Nat.testBit_two_pow_sub_succ (UInt64.toNat_lt _), Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, Nat.mod_lt _ (by omega : 0 < 64), true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; exact Bool.false_ne_true⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2⟩

theorem bitsIs_fold (p : Nat → Bool) (g : Nat → Nat) : ∀ n, (∀ x < n, p x = true → g x < 3520) →
    BitsIs (Nat.fold n (fun x _ C => if p x = true then setBit C (g x) else C) (emptyBits ()))
      fun y => ∃ x < n, p x = true ∧ g x = y
  | 0, _ => by
    rw [Nat.fold_zero]
    exact bitsIs_empty.congr fun y _ => by simp
  | n + 1, hg => by
    rw [Nat.fold_succ]
    have ih := bitsIs_fold p g n fun x hx => hg x (by omega)
    by_cases hp : p n = true
    · rw [if_pos hp]
      refine (bitsIs_setBit ih (hg n (by omega) hp)).congr fun y _ => ?_
      constructor
      · rintro (⟨x, hx, h1, h2⟩ | h)
        · exact ⟨x, by omega, h1, h2⟩
        · exact ⟨n, by omega, hp, h.symm⟩
      · rintro ⟨x, hx, h1, h2⟩
        rcases Nat.lt_or_ge x n with h | h
        · exact Or.inl ⟨x, h, h1, h2⟩
        · have : x = n := by omega
          subst this
          exact Or.inr h2.symm
    · rw [if_neg hp]
      refine ih.congr fun y _ => ?_
      constructor
      · rintro ⟨x, hx, h1, h2⟩
        exact ⟨x, by omega, h1, h2⟩
      · rintro ⟨x, hx, h1, h2⟩
        rcases Nat.lt_or_ge x n with h | h
        · exact ⟨x, h, h1, h2⟩
        · have : x = n := by omega
          subst this
          exact absurd h1 hp

theorem bitsIs_imgBits {T : Table} {B : Bits} {S : Nat → Prop} (hB : BitsIs B S)
    (hT : ∀ x < 3510, S x → ap T x < 3520) :
    BitsIs (imgBits T B) fun y => ∃ x < 3510, S x ∧ ap T x = y := by
  unfold imgBits
  refine (bitsIs_fold (bitAt B) (ap T) 3510 fun x hx h => hT x hx ((hB.2 x (by omega)).1 h)).congr
    fun y _ => ?_
  constructor
  · rintro ⟨x, hx, h1, h2⟩
    exact ⟨x, hx, (hB.2 x (by omega)).1 h1, h2⟩
  · rintro ⟨x, hx, h1, h2⟩
    exact ⟨x, hx, (hB.2 x (by omega)).2 h1, h2⟩

end CFSG.KS.Fi22LH
